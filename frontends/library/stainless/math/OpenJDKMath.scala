package stainless
package math

import stainless.lang.*
import stainless.annotation.*

@library
object OpenJDKMath {
  object DoubleConsts {
    /**
     * Bias used in representing a {@code double} exponent.
     */
    val EXP_BIAS = 1023
    /**
     * Bit mask to isolate the exponent field of a {@code double}.
     */
    val EXP_BIT_MASK = 0x7FF0000000000000L
    /**
     * Bit mask to isolate the significand field of a {@code double}.
     */
    val SIGNIF_BIT_MASK = 0x000FFFFFFFFFFFFFL
    /**
     * The number of logical bits in the significand of a
     * {@code double} number, including the implicit bit.
     */
    val SIGNIFICAND_WIDTH: Int = 53
    /**
     * A constant holding the smallest positive nonzero value of type
     * {@code double}, 2<sup>-1074</sup>. It is equal to the
     * hexadecimal floating-point literal
     * {@code 0x0.0000000000001P-1022} and also equal to
     * {@code Double.longBitsToDouble(0x1L)}.
     */
    val MIN_VALUE = 4.94065645841246544177e-324
  }

  def floor(a: Double): Double = floorOrCeil(a, -1.0, 0.0, -1.0)

  def ceil(a: Double): Double = floorOrCeil(a, -0.0, 1.0, 1.0)

  def getExponent(d: Double): Int = {
    val bits = (java.lang.Double.doubleToRawLongBits(d) & DoubleConsts.EXP_BIT_MASK) >> (DoubleConsts.SIGNIFICAND_WIDTH - 1)
    (bits - DoubleConsts.EXP_BIAS).toInt
  }

  /**
   * Internal method to share logic between floor and ceil.
   *
   * @param a                the value to be floored or ceiled
   * @param negativeBoundary result for values in (-1, 0)
   * @param positiveBoundary result for values in (0, 1)
   * @param sign             the sign of the result
   */
  @extern
  private def floorOrCeil(a: Double, negativeBoundary: Double, positiveBoundary: Double, sign: Double): Double = {
    val exponent = getExponent(a)
    if (exponent < 0) {
      /*
       * Absolute value of argument is less than 1.
       * floorOrCeil(-0.0) => -0.0
       * floorOrCeil(+0.0) => +0.0
       */
      return if (a == 0.0) a
      else if (a < 0.0) negativeBoundary
      else positiveBoundary
    }
    else if (exponent >= 52) {
      /*
       * Infinity, NaN, or a value so large it must be integral.
       */
      return a
    }
    // Else the argument is either an integral value already XOR it
    // has to be rounded to one.
    assert(exponent >= 0 && exponent <= 51)
    val doppel = java.lang.Double.doubleToRawLongBits(a)
    val mask = DoubleConsts.SIGNIF_BIT_MASK >> exponent
    if ((mask & doppel) == 0L) a // integral value
    else {
      var result = java.lang.Double.longBitsToDouble(doppel & (~mask))
      if (sign * a > 0.0) result = result + sign
      result
    }
  }

  /**
   * Returns a floating-point power of two in the normal range.
   * No checks are performed on the argument.
   */
  @extern
  private def primPowerOfTwoD(n: Int) = java.lang.Double.longBitsToDouble(
    (n + DoubleConsts.EXP_BIAS).asInstanceOf[Long] << DoubleConsts.SIGNIFICAND_WIDTH - 1)

  private val F_UP = 8.98846567431157953865e+307 // 0x1p1023, normal, exact, 2^DoubleConsts.EXP_BIAS
  private val F_DOWN = 1.11253692925360069155e-308 // 0x1p-1023 subnormal, exact, 2^-DoubleConsts.EXP_BIAS

  /**
   * Returns {@code d} &times; 2<sup>{@code scaleFactor}</sup>
   * rounded as if performed by a single correctly rounded
   * floating-point multiply.  If the exponent of the result is
   * between {@link Double# MIN_EXPONENT} and {@link    * Double#MAX_EXPONENT}, the answer is calculated exactly.  If the
   * exponent of the result would be larger than {@code
   * Double.MAX_EXPONENT}, an infinity is returned.  Note that if
   * the result is subnormal, precision may be lost; that is, when
   * {@code scalb(x, n)} is subnormal, {@code scalb(scalb(x, n),
     * -n)} may not equal <i>x</i>.  When the result is non-NaN, the
   * result has the same sign as {@code d}.
   *
   * <p>Special cases:
   * <ul>
   * <li> If the first argument is NaN, NaN is returned.
   * <li> If the first argument is infinite, then an infinity of the
   * same sign is returned.
   * <li> If the first argument is zero, then a zero of the same
   * sign is returned.
   * </ul>
   *
   * @apiNote This method corresponds to the scaleB operation
   *          defined in IEEE 754.
   * @param d           number to be scaled by a power of two.
   * @param scaleFactor power of 2 used to scale {@code d}
   * @return {@code d} &times; 2<sup>{@code scaleFactor}</sup>
   * @since 1.6
   */
  @extern @pure
  def scalb(d: Double, scaleFactor: Int): Double = {
    if (scaleFactor > -DoubleConsts.EXP_BIAS)
      if (scaleFactor <= DoubleConsts.EXP_BIAS)
        d * primPowerOfTwoD(scaleFactor)
      else if (scaleFactor <= 2 * DoubleConsts.EXP_BIAS)
        d * primPowerOfTwoD(scaleFactor - DoubleConsts.EXP_BIAS) * F_UP
      else if (scaleFactor < 2 * DoubleConsts.EXP_BIAS + DoubleConsts.SIGNIFICAND_WIDTH - 1)
        d * primPowerOfTwoD(scaleFactor - 2 * DoubleConsts.EXP_BIAS) * F_UP * F_UP
      else d * F_UP * F_UP * F_UP
    else
      if (scaleFactor > -2 * DoubleConsts.EXP_BIAS)
        d * primPowerOfTwoD(scaleFactor + DoubleConsts.EXP_BIAS) * F_DOWN
      else if (scaleFactor > -2 * DoubleConsts.EXP_BIAS - DoubleConsts.SIGNIFICAND_WIDTH)
        d * primPowerOfTwoD(scaleFactor + 2 * DoubleConsts.EXP_BIAS) * F_DOWN * F_DOWN
      else d * DoubleConsts.MIN_VALUE * DoubleConsts.MIN_VALUE
  }

  @ignore
  def main(args: Array[String]): Unit = {
    val scaleFactor = 567
    var i = Int.MinValue
    while (i != Int.MaxValue) {
      val d = java.lang.Float.intBitsToFloat(i).toDouble
      val s1 = scalb(d, scaleFactor)
      val s2 = Math.scalb(d, scaleFactor)
      if (i % 100000000 == 0)
        println(s"progress: $d  s1: $s1")
      val diff = Math.abs(s1 - s2)
      val ulp = Math.min(Math.ulp(s1), Math.ulp(s2))
      if !s1.equiv(s2) then {
        println(s"error: d = $d, diff = $diff, s1 = $s1, s2 = $s2, ulp(s1) = ${Math.ulp(s1)}, ulp(s2r) = ${Math.ulp(s2)}")
        i = Int.MaxValue
      }
      else
        i += 1
    }
  }
}
