package com.stripe.rainier.core

import com.stripe.rainier.compute._

/**
  * Predictor class, for fitting data with covariates
  */
sealed trait Predictor[L, X] { self =>
  type P
  protected def xp: Placeholder[X, P]
  protected def create(p: P): L

  def fit[Y](values: Seq[(X, Y)])(
      implicit lh: ToLikelihood[L, Y]): RandomVariable[Predictor[L, X]] =
    Predictor
      .likelihood[L, X, Y](this)
      .fit(values)
      .map { _ =>
        this
      }

  def predict[Y](x: X)(implicit gen: ToGenerator[L, Y]): Generator[Y] =
    ??? //gen(create(wrap(x))

  def predict[Y](seq: Seq[X])(
      implicit gen: ToGenerator[L, Y]): Generator[Seq[(X, Y)]] =
    Generator.traverse(seq.map { x =>
      predict(x).map { y =>
        (x, y)
      }
    })
}

object Predictor {
  def likelihood[L, X, Y](pred: Predictor[L, X])(
      implicit lh: ToLikelihood[L, Y]): Likelihood[(X, Y)] = {
    val p = pred.xp.create()
    val l = pred.create(p)
    val inner = lh(l)
    new Likelihood[(X, Y)] {
      val real = inner.real
      val variables = pred.xp.variables(p, inner.variables)
      def extract(t: (X, Y)) =
        pred.xp.extract(t._1, inner.extract(t._2))
    }
  }

  class Fitter[X, A, Y](seq: Seq[(X, Y)], xa: Placeholder[X, A]) {
    val maker = new Maker(xa)
    def to[B](fn: A => B)(
        implicit lh: ToLikelihood[B, Y]): RandomVariable[Predictor[B, X]] =
      maker(fn).fit(seq)
  }

  def fit[X, Y, A, B](seq: Seq[(X, Y)])(implicit xa: Placeholder[X, A]) =
    new Fitter(seq, xa)

  class Maker[X, A](xa: Placeholder[X, A]) {
    def apply[B](fn: A => B): Predictor[B, X] =
      new Predictor[B, X] {
        type P = A
        val xp = xa
        def create(p: P) = fn(p)
      }
  }

  def from[X, A](implicit xa: Placeholder[X, A]) = new Maker(xa)
  def fromInt = from[Int, Variable]
  def fromDouble = from[Double, Variable]
  def fromIntPair = from[(Int, Int), (Variable, Variable)]
  def fromDoublePair = from[(Double, Double), (Variable, Variable)]
  def fromIntVector(size: Int) =
    from[Seq[Int], Seq[Variable]](Placeholder.vector(size))
  def fromDoubleVector(size: Int) =
    from[Seq[Double], Seq[Variable]](Placeholder.vector(size))
}
