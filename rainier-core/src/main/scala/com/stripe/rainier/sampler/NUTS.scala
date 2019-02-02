package com.stripe.rainier.sampler

import scala.collection.mutable.ListBuffer

/**
  * No-u-turn sampler with dual averaging
  * @param l0 the initial number of leapfrog steps
  * @param delta the target acceptance rate
  * @param deltamax if pos(theta) - log(u) < deltamax stop) extends Sampler {
  */
final case class NUTS(l0: Int = 10,
                      delta: Double = 0.65,
                      deltamax: Double = 1000) {
  def sample(density: DensityFunction,
             warmupIterations: Int,
             iterations: Int,
             keepEvery: Int)(implicit rng: RNG): List[Array[Double]] = {

    val lf = LeapFrog(density)
    val params = lf.initialize
    val stepSize =
      DualAvg.findStepSize(lf, params, delta, l0, warmupIterations)

    if (stepSize == 0.0)
      List(lf.variables(params))
    else {
      val buf = new ListBuffer[Array[Double]]
      var i = 0

      while (i < iterations) {
        lf.stepNuts(deltamax, params, stepSize)
        if (i % keepEvery == 0)
          buf += lf.variables(params)
        i += 1
      }
      buf.toList
    }
  }
}
