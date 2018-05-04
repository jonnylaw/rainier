package rainier.compute

import org.scalatest._
import rainier.compute
import rainier.core._

class RealTest extends FunSuite {
  def run(description: String)(fn: Real => Real): Unit = {
    test(description) {
      val x = new Variable
      val result = fn(x)
      List(0.0, -1.0, 1.0, 2.0, -2.0, 0.5, -0.5).foreach { n =>
        val constant = fn(Constant(n))
        assert(constant.isInstanceOf[Constant], s"[n=$n]")
        val eval = new Evaluator(Map(x -> n))
        val withVar = eval.toDouble(result)
        assertWithinEpsilon(constant.asInstanceOf[Constant].value,
                            withVar,
                            s"[n=$n]")
      }
    }
  }

  def assertWithinEpsilon(x: Double, y: Double, clue: String): Unit = {
    assert(x == y || (x - y) < 0.000000001, clue)
  }

  run("plus") { x =>
    x + 1
  }
  run("exp") { x =>
    x.exp
  }
  run("square") { x =>
    x * x
  }
  run("log") { x =>
    x.abs.log
  }
  run("temp") { x =>
    val t = x * 3
    t + t
  }
  run("normal") { x =>
    Normal(x, 1).logDensities(0d.to(2d).by(1).toList)
  }

  run("logistic") { x =>
    val logistic = Real.one / (Real.one + (x * -1).exp)
    val density = (logistic * (Real.one - logistic)).log
    density
  }

  run("poisson") { x =>
    Poisson(x.abs + 1).logDensities(0.to(10).toList)
  }
}
