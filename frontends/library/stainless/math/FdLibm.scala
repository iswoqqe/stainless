package stainless
package math

import stainless.annotation.*
import stainless.lang.*
import stainless.math.wrapping

object FdLibm {
  private val TWO24 = 1.67772160000000000000e+07 // 0x1.0p24
  private val EXP_SIGNIF_BITS = 0x7fff_ffff
  private val EXP_BITS = 0x7ff0_0000

  private def __LO(x: Double): Int = {
    val transducer = java.lang.Double.doubleToLongBits(x)
    wrapping(transducer.toInt)
  }

  private def __LO(x: Double, low: Int): Double = {
    val transX = java.lang.Double.doubleToLongBits(x)
    java.lang.Double.longBitsToDouble((transX & 0xFFFF_FFFF_0000_0000L) | (low & 0x0000_0000_FFFF_FFFFL))
  }

  private def __HI(x: Double): Int = {
    val transducer = java.lang.Double.doubleToLongBits(x)
    (transducer >> 32).toInt
  }

  private def __HI(x: Double, high: Int): Double = {
    val transX = java.lang.Double.doubleToLongBits(x)
    java.lang.Double.longBitsToDouble((transX & 0x0000_0000_FFFF_FFFFL) | high.toLong << 32)
  }

  private def __HI_LO(high: Int, low: Int): Double = {
    java.lang.Double.longBitsToDouble((high.toLong << 32) | (low & 0xffff_ffffL))
  }

  object Sin {
    @opaque
    def sin(x: Double): Double = {
      val ix = __HI(x) & EXP_SIGNIF_BITS
      if (ix <= 0x3fe9_21fb) // |x| ~< pi / 4
        unfold(__kernel_sin(x, 0.0d, 0))
        __kernel_sin(x, 0.0d, 0)
      else if (ix >= EXP_BITS) // sin(Inf or NaN) is NaN
        x - x
      else {
        val (n, y0, y1) = RemPio2.__ieee754_rem_pio2(x)
        n & 3 match {
          case 0 => Sin.__kernel_sin(y0, y1, 1)
          case 1 => Cos.__kernel_cos(y0, y1)
          case 2 => -Sin.__kernel_sin(y0, y1, 1)
          case _ => -Cos.__kernel_cos(y0, y1)
        }
      }
    }.ensuring(res =>
      (!x.isFinite == res.isNaN)
        && (x.equiv(+0.0d) ==> res.equiv(+0.0d))
        && (x.equiv(-0.0d) ==> res.equiv(-0.0d))
        && (-1.0d <= res && res <= 1.0d || res.isNaN)
    )

    private val S1 = -1.66666666666666324348e-01d // -0x1.5555555555549p-3
    private val S2 = 8.33333333332248946124e-03d // 0x1.111111110f8a6p-7
    private val S3 = -1.98412698298579493134e-04d // -0x1.a01a019c161d5p-13
    private val S4 = 2.75573137070700676789e-06d // 0x1.71de357b1fe7dp-19
    private val S5 = -2.50507602534068634195e-08d // -0x1.ae5e68a2b9cebp-26
    private val S6 = 1.58969099521155010221e-10d // 0x1.5d93a5acfd57cp-33

    @opaque
    def __kernel_sin(x: Double, y: Double, iy: Int): Double = {
      require(-0.7854 <= x && x <= 0.7854)
      require(-1.1102230246251565E-16 <= y && y <= 1.1102230246251565E-16)
      val ix = __HI(x) & EXP_SIGNIF_BITS
      if (ix < 0x3e40_0000) { // abs(x) < 7.450580596923828125e-9
        if (x.toInt == 0)
          return x
      }

      val z = x*x
      val v = z*x
      val r = S2 + z*(S3 + z*(S4 + z*(S5 + z*S6)))
      assert(0.0d <= r && r <= S2)

      if (iy == 0)
        x + v * (S1 + z * r)
      else
        x - ((z*(0.5d*y - v*r) - y) - v*S1)
    }.ensuring(res => -1.0d <= res && res <= 1.0d) // very loose bounds
  }

  object Cos {
    @opaque
    def cos(x: Double): Double = {
      val ix = __HI(x) & EXP_SIGNIF_BITS
      if (ix <= 0x3fe9_21fb) // |x| ~< pi / 4
        __kernel_cos(x, 0.0d)
      else if (ix >= EXP_BITS) // sin(Inf or NaN) is NaN
        x - x
      else {
        val (n, y0, y1) = RemPio2.__ieee754_rem_pio2(x)
        n & 3 match {
          case 0 => Cos.__kernel_cos(y0, y1)
          case 1 => -Sin.__kernel_sin(y0, y1, 1)
          case 2 => -Cos.__kernel_cos(y0, y1)
          case _ => Sin.__kernel_sin(y0, y1, 1)
        }
      }
    }.ensuring(res =>
      (!x.isFinite == res.isNaN)
        && (-1.0d <= res && res <= 1.0d || res.isNaN)
    )

    private val C1 =  4.16666666666666019037e-02d //  0x1.555555555554cp-5
    private val C2 = -1.38888888888741095749e-03d // -0x1.6c16c16c15177p-10
    private val C3 =  2.48015872894767294178e-05d //  0x1.a01a019cb159p-16
    private val C4 = -2.75573143513906633035e-07d // -0x1.27e4f809c52adp-22
    private val C5 =  2.08757232129817482790e-09d //  0x1.1ee9ebdb4b1c4p-29
    private val C6 = -1.13596475577881948265e-11d // -0x1.8fae9be8838d4p-37

    @opaque
    def __kernel_cos(x: Double, y: Double): Double = {
      require(-0.7854 <= x && x <= 0.7854)
      require(-1.1102230246251565E-16 <= y && y <= 1.1102230246251565E-16)
      val ix = __HI(x) & EXP_SIGNIF_BITS
      if (ix < 0x3e40_0000) { // abs(x) < 7.450580596923828125e-9
        if (x.toInt == 0)
          return 1.0d
      }

      val z = x*x
      val r = z*(C1 + z*(C2 + z*(C3 + z*(C4 + z*(C5 + z*C6)))))
      assert(0 <= r && r <= 0.785398483276367076478d*0.785398483276367076478d*C1)

      if (ix < 0x3FD3_3333) // |x| < 0.3
        1.0 - (0.5*z - (z*r - x*y))
      else {
        val qx = if (ix > 0x3fe9_0000) // x > 0.78125
          0.28125d
        else
          __HI_LO(ix - 0x0020_0000, 0)
        val hz = 0.5d*z - qx
        val a  = 1.0d - qx
        a - (hz - (z*r - x*y))
      }
    }.ensuring(res => -1.0d <= res && res <= 1.0d) // very loose bounds
  }

  object RemPio2 {
    private val npio2_hw = Array[Int](
      0x3FF921FB, 0x400921FB, 0x4012D97C, 0x401921FB, 0x401F6A7A, 0x4022D97C,
      0x4025FDBB, 0x402921FB, 0x402C463A, 0x402F6A7A, 0x4031475C, 0x4032D97C,
      0x40346B9C, 0x4035FDBB, 0x40378FDB, 0x403921FB, 0x403AB41B, 0x403C463A,
      0x403DD85A, 0x403F6A7A, 0x40407E4C, 0x4041475C, 0x4042106C, 0x4042D97C,
      0x4043A28C, 0x40446B9C, 0x404534AC, 0x4045FDBB, 0x4046C6CB, 0x40478FDB,
      0x404858EB, 0x404921FB)

    private val invpio2 = 6.36619772367581382433e-01d // 0x1.45f306dc9c883p-1
    private val pio2_1  = 1.57079632673412561417e+00d // 0x1.921fb544p0
    private val pio2_1t = 6.07710050650619224932e-11d // 0x1.0b4611a626331p-34
    private val pio2_2  = 6.07710050630396597660e-11d // 0x1.0b4611a6p-34
    private val pio2_2t = 2.02226624879595063154e-21d // 0x1.3198a2e037073p-69
    private val pio2_3  = 2.02226624871116645580e-21d // 0x1.3198a2ep-69
    private val pio2_3t = 8.47842766036889956997e-32d // 0x1.b839a252049c1p-104

    @opaque
    def __ieee754_rem_pio2(x: Double): (Int, Double, Double) = {
      val hx = __HI(x)
      val ix = hx & EXP_SIGNIF_BITS
      if (ix >= EXP_BITS) { // x is inf or NaN
        assert(!x.isFinite)
        (0, x - x, x - x)
      }
      else if (ix <= 0x3fe9_21fb) { // |x| ~<= pi/4 , no need for reduction
        assert(-0.785398483276367076478d <= x && x <= 0.785398483276367076478d)
        (0, x, 0d)
      }
      else if (ix < 0x4002_d97c) { // |x| < 3pi/4, special case with n=+-1
        assert(-2.35619354248046875d < x && x < -0.785398483276367076478d || 0.785398483276367076478d < x && x < 2.35619354248046875d)
        if (hx > 0) { // positive x
          if (ix != 0x3ff9_21fb) { // 33+53 bit pi is good enough
            val z = x - pio2_1
            (1, z - pio2_1t, (z - (z - pio2_1t)) - pio2_1t)
          } else { // near pi/2, use 33+33+53 bit pi
            val z = (x - pio2_1) - pio2_2
            (1, z - pio2_2t, (z - (z - pio2_2t)) - pio2_2t)
          }
        } else { // negative x
          if (ix != 0x3ff_921fb) { // 33+53 bit pi is good enough
            val z = x + pio2_1
            (-1, z + pio2_1t, (z - (z + pio2_1t)) + pio2_1t)
          } else { // near pi/2, use 33+33+53 bit pi
            val z = (x + pio2_1) + pio2_2
            (-1, z + pio2_2t, (z - (z + pio2_2t)) + pio2_2t)
          }
        }
      }
      // We skip this case for now since it is currently too challenging for SMT-solvers.
      // It would likely take several days for a proof, unless we find some "smart" solution.
//      else if (ix <= 0x4139_21fb) { // |x| ~<= 2^19*(pi/2), medium size // TODO: should this not say 2^20??
//        assume(-1647099.99999999976717d <= x && x <= -2.35619354248046875d || 2.35619354248046875d <= x && x <= 1647099.99999999976717d) // TODO
//        val j = ix >> 20
//        val abs_x = if x.isNegative then -x else x // Math.abs(x)
//        assert(2.35619354248046875d <= abs_x && abs_x <= 1647099.99999999976717d)
//        val n = (abs_x * invpio2 + 0.5).toInt
//        val fn = n.toDouble
//        assert(1 <= n && n <= 1048576)
//        val r0 = abs_x - fn * pio2_1 // 1st round good to 85 bit
//        assert(-0.7854618860874325 <= r0 && r0 <= 0.7854618860874325)
//        val w0 = fn * pio2_1t
//        val y0 = r0 - w0
//        val (yy0, yy1) = if (n < 32 && ix != npio2_hw(n - 1) || j - ((__HI(y0) >> 20) & 0x7ff) <= 16) {
//          (y0, (r0 - y0) - w0)
//        } else { // 2nd iteration needed, good to 118
//          assume(16 * (if y0 < 0 then -y0 else y0) < (if x < 0 then -x else x)) // TODO
//          val r1 = r0 - fn * pio2_2
//          val w1 = fn * pio2_2t - ((r0 - r1) - fn * pio2_2)
//          val y1 = r1 - w1
//          if (j - ((__HI(y1) >> 20) & 0x7ff) <= 49) {
//            (y1, (r1 - y1) - w1)
//          } else { // 3rd iteration need, 151 bits acc, will cover all possible cases
//            assume(49 * (if y0 < 0 then -y0 else y0) < (if x < 0 then -x else x)) // TODO
//            val r2 = r1 - fn * pio2_3
//            val w2 = fn * pio2_3t - ((r1 - r2) - fn * pio2_3)
//            val y2 = r2 - w2
//            (y2, (r2 - y2) - w2)
//          }
//        }
//        if hx < 0 then (-n, -yy0, -yy1) else (n, yy0, yy1)
//      }
      else { // all other (large) arguments
        assert(x <= -2.35619354248046875d || 2.35619354248046875d <= x)
        val abs = if hx < 0 then -x else x
        val (n1, y0, y1) = KernelRemPio2.__kernel_rem_pio2(abs)
        if hx < 0 then (-n1, -y0, -y1) else (n1, y0, y1)
      }
    }.ensuring(res =>
      (!x.isFinite) ||
        (-8 < res._1 && res._1 < 8
          && -0.785398483276367076478d <= res._2 && res._2 <= 0.785398483276367076478d
          && -1.1102230246251565E-16 <= res._3 && res._3 <= 1.1102230246251565E-16)
    )
  }
  
  object KernelRemPio2 {
    // This object is based on the OpenJDK class `KernelRemPio2`, with modifications to simplify Stainless proofs.
    // Some of the main changes:
    // - the signature of `__kernel_rem_pio2()` has been changed
    //   - it now accepts doubles as inputs, not arrays of 24-bit chunks of numbers (here, we only care about doubles anyway)
    //   - the result is now computed with constant precision, not an argument-dependant precision
    // - the body of `__kernel_rem_pio2()` has been split into several methods to clarify the structure of the algorithm
    // - the input splitting may pad the input with leading zeros to ensure that the exponent of `q(0)` is always zero
    // - the product of the input and two over pi is now evaluated using a constant precision, not an adaptive precision like in the original
    //   - but, adaptive precision can probably be added again as a performance optimization
    // - the compression of the result into a double-double is implemented in a different way to allow for a simple loop invariant
    // - some loops are partially unrolled to help the SMT-solvers
    // - new functions and constants for proof annotations have been added

    //// Constants ////

    private val two_over_pi = Array[Int]( // moved to this object from RemPio2
      0xA2F983, 0x6E4E44, 0x1529FC, 0x2757D1, 0xF534DD, 0xC0DB62,
      0x95993C, 0x439041, 0xFE5163, 0xABDEBB, 0xC561B7, 0x246E3A,
      0x424DD2, 0xE00649, 0x2EEA09, 0xD1921C, 0xFE1DEB, 0x1CB129,
      0xA73EE8, 0x8235F5, 0x2EBB44, 0x84E99C, 0x7026B4, 0x5F7E41,
      0x3991D6, 0x398353, 0x39F49C, 0x845F8B, 0xBDF928, 0x3B1FF8,
      0x97FFDE, 0x05980F, 0xEF2F11, 0x8B5A0A, 0x6D1F6D, 0x367ECF,
      0x27CB09, 0xB74F46, 0x3F669E, 0x5FEA2D, 0x7527BA, 0xC7EBE5,
      0xF17B3D, 0x0739F7, 0x8A5292, 0xEA6BFB, 0x5FB11F, 0x8D5D08,
      0x560330, 0x46FC7B, 0x6BABF0, 0xCFBC20, 0x9AF436, 0x1DA9E3,
      0x91615E, 0xE61B08, 0x659985, 0x5F14A0, 0x68408D, 0xFFD880,
      0x4D7327, 0x310606, 0x1556CA, 0x73A8C9, 0x60E27B, 0xC08C6B)

    private val PIo2 = Array[Double](
      1.57079625129699707031e+00d, // 0x1.921fb4p0,
      7.54978941586159635335e-08d, // 0x1.4442dp-24,
      5.39030252995776476554e-15d, // 0x1.846988p-48,
      3.28200341580791294123e-22d, // 0x1.8cc516p-72,
      1.27065575308067607349e-29d, // 0x1.01b838p-96,
      1.22933308981111328932e-36d, // 0x1.a25204p-120,
      2.73370053816464559624e-44d, // 0x1.382228p-145,
      2.16741683877804819444e-51d) // 0x1.9f31dp-169,

    private val twon24 = 5.96046447753906250000e-08d // 0x1.0p-24

    private val twon24Pow = Array[Double](
      1,
      5.9604644775390625E-8,
      3.552713678800501E-15,
      2.1175823681357508E-22,
      1.2621774483536189E-29,
      7.52316384526264E-37,
      4.4841550858394146E-44,
      2.6727647100921956E-51,
      1.5930919111324523E-58,
      9.495567745759799E-66,
      5.659799424266695E-73,
      3.3735033418337674E-80,
      2.0107646833859488E-87,
      1.1985091468012028E-94,
      7.143671195514219E-102,
      4.2579598400081507E-109,
      2.5379418373156492E-116,
      1.512731216738015E-123,
      9.016580681431383E-131,
      5.374300886053671E-138
    )

    //// Helpers for expressing invariants ////

    @pure
    private def all5(a: Array[Double], P: Double => Boolean): Boolean = {
      require(a.length == 5)
      P(a(0)) && P(a(1)) && P(a(2)) && P(a(3)) && P(a(4))
    }

    @pure
    private def all20(a: Array[Double], P: Double => Boolean): Boolean = {
      require(a.length == 20)
      P(a(0)) && P(a(1)) && P(a(2)) && P(a(3)) && P(a(4)) && P(a(5)) && P(a(6)) && P(a(7)) && P(a(8)) && P(a(9)) && P(a(10)) && P(a(11)) && P(a(12)) && P(a(13)) && P(a(14)) && P(a(15)) && P(a(16)) && P(a(17)) && P(a(18)) && P(a(19))
    }

    @pure
    private def all20Int(a: Array[Int], P: Int => Boolean): Boolean = {
      require(a.length == 20)
      P(a(0)) && P(a(1)) && P(a(2)) && P(a(3)) && P(a(4)) && P(a(5)) && P(a(6)) && P(a(7)) && P(a(8)) && P(a(9)) && P(a(10)) && P(a(11)) && P(a(12)) && P(a(13)) && P(a(14)) && P(a(15)) && P(a(16)) && P(a(17)) && P(a(18)) && P(a(19))
    }

    private def P(x: Double): Boolean = 0 <= x && x <= 5 * 0xffff_ffff_ffffL

    private def Q(x: Double): Boolean = 0 <= x && x <= 0xff_ffff

    private def QInt(x: Int): Boolean = 0 <= x && x <= 0xff_ffff

    //// Invariants and bound arrays ////

    @pure
    private def xxInv(xx: Array[Double]): Boolean = xx.length == 5 && all5(xx, Q)

    @pure
    private def fInv(f: Array[Double]): Boolean = f.length == 20 && all20(f, Q)

    @pure
    private def qInv(q: Array[Double]): Boolean = q.length == 20 && all20(q, P)

    @pure
    private def iqInv(iq: Array[Int]): Boolean = iq.length == 20 && all20Int(iq, QInt)

    private val qqBound = Array[Double](
      0.4999999403953552,
      5.9604641222676946E-8,
      3.552713467042264E-15,
      2.117582241918006E-22,
      1.2621773731219804E-29,
      7.5231633968471315E-37,
      4.4841548185629436E-44,
      2.6727645507830045E-51,
      1.5930918161767748E-58,
      9.495567179779856E-66,
      5.659799086916361E-73,
      3.373503140757299E-80,
      2.0107645635350341E-87,
      1.1985090753644908E-94,
      7.143670769718235E-102,
      4.257959586213967E-109,
      2.5379416860425275E-116,
      1.5127311265722081E-123,
      9.016580144001294E-131,
      5.374300565720376E-138,
    )

    @pure
    private def qqInv(qq: Array[Double]): Boolean = {
      qq.length == 20
        && 0 <= qq(0) && qq(0) <= 0.4999999403953552 // replacing this by `qqBound(0)` etc. seems to have a negative impact on solver performance
        && 0 <= qq(1) && qq(1) <= 5.9604641222676946E-8
        && 0 <= qq(2) && qq(2) <= 3.552713467042264E-15
        && 0 <= qq(3) && qq(3) <= 2.117582241918006E-22
        && 0 <= qq(4) && qq(4) <= 1.2621773731219804E-29
        && 0 <= qq(5) && qq(5) <= 7.5231633968471315E-37
        && 0 <= qq(6) && qq(6) <= 4.4841548185629436E-44
        && 0 <= qq(7) && qq(7) <= 2.6727645507830045E-51
        && 0 <= qq(8) && qq(8) <= 1.5930918161767748E-58
        && 0 <= qq(9) && qq(9) <= 9.495567179779856E-66
        && 0 <= qq(10) && qq(10) <= 5.659799086916361E-73
        && 0 <= qq(11) && qq(11) <= 3.373503140757299E-80
        && 0 <= qq(12) && qq(12) <= 2.0107645635350341E-87
        && 0 <= qq(13) && qq(13) <= 1.1985090753644908E-94
        && 0 <= qq(14) && qq(14) <= 7.143670769718235E-102
        && 0 <= qq(15) && qq(15) <= 4.257959586213967E-109
        && 0 <= qq(16) && qq(16) <= 2.5379416860425275E-116
        && 0 <= qq(17) && qq(17) <= 1.5127311265722081E-123
        && 0 <= qq(18) && qq(18) <= 9.016580144001294E-131
        && 0 <= qq(19) && qq(19) <= 5.374300565720376E-138
    }

    private val fqBound = Array[Double](
      0.785398032021746,
      1.3137568957176623E-7,
      1.2775764834046103E-14,
      1.0862386096603872E-21,
      8.087927686569757E-29,
      5.199465491241273E-36,
      3.09912293627338E-43,
      1.8472212173184038E-50,
      1.101029644798281E-57,
      6.562648086537606E-65,
      3.91164307983971E-72,
      2.3315209626196086E-79,
      1.3896947876331858E-86,
      8.283226416308795E-94,
      4.937187681382176E-101,
      2.942793179382191E-108,
      1.7540414210451787E-115,
      1.0454901582271926E-122,
      6.231606949729875E-130,
      3.714327186185047E-137,
    )

    @pure
    private def fqInv(fq: Array[Double]): Boolean = {
      fq.length == 20
        && 0 <= fq(0) && fq(0) <= 0.785398032021746
        && 0 <= fq(1) && fq(1) <= 1.3137568957176623E-7
        && 0 <= fq(2) && fq(2) <= 1.2775764834046103E-14
        && 0 <= fq(3) && fq(3) <= 1.0862386096603872E-21
        && 0 <= fq(4) && fq(4) <= 8.087927686569757E-29
        && 0 <= fq(5) && fq(5) <= 5.199465491241273E-36
        && 0 <= fq(6) && fq(6) <= 3.09912293627338E-43
        && 0 <= fq(7) && fq(7) <= 1.8472212173184038E-50
        && 0 <= fq(8) && fq(8) <= 1.101029644798281E-57
        && 0 <= fq(9) && fq(9) <= 6.562648086537606E-65
        && 0 <= fq(10) && fq(10) <= 3.91164307983971E-72
        && 0 <= fq(11) && fq(11) <= 2.3315209626196086E-79
        && 0 <= fq(12) && fq(12) <= 1.3896947876331858E-86
        && 0 <= fq(13) && fq(13) <= 8.283226416308795E-94
        && 0 <= fq(14) && fq(14) <= 4.937187681382176E-101
        && 0 <= fq(15) && fq(15) <= 2.942793179382191E-108
        && 0 <= fq(16) && fq(16) <= 1.7540414210451787E-115
        && 0 <= fq(17) && fq(17) <= 1.0454901582271926E-122
        && 0 <= fq(18) && fq(18) <= 6.231606949729875E-130
        && 0 <= fq(19) && fq(19) <= 3.714327186185047E-137
    }

    private val sBound = Array[Double](
      0.7853981633974483,
      1.3137570234753214E-7,
      1.2775765920284793E-14,
      1.0862386905396692E-21,
      8.087928206516337E-29,
      5.1994658011535854E-36,
      3.099123120995513E-43,
      1.8472213274213748E-50,
      1.1010297104247658E-57,
      6.562648477701937E-65,
      3.91164331299182E-72,
      2.3315211015890957E-79,
      1.3896948704654549E-86,
      8.283226910027593E-94,
      4.937187975661512E-101,
      2.9427933547863434E-108,
      1.7540415255942007E-115,
      1.0454902205432658E-122,
      6.2316073211625935E-130,
      3.714327186185047E-137,
    )

    //// Implementations of the main parts of the algorithm ////

    /**
     * Split the input into an array of 24-bit integer chunks, represented using doubles.
     * Leading zeros may be inserted to ensure the exponents of the chunks are multiples of `24`.
     * @param x finite double to split
     * @return `(e, xx)` where `e % 24 == 0` and `x == (for (i <- 0 to 4) yield xx[i] * math.scalb(1.0d, e - 24 * i)).sum` TODO: test
     */
    @opaque @pure
    private def splitInput(x: Double): (Int, Array[Double]) = {
      require(1 <= x && x.isFinite)
      val hx = __HI(x)
      val ix = hx & EXP_SIGNIF_BITS
      val e0 = (ix >> 20) - 1046 // exponent - 23
      assert(-23 <= e0 && e0 <= 1000)
      val e = {
        val tmp = 24 * ((e0 + 23) / 24)
        if tmp < 24 then 24 else tmp
      }
      assert(24 <= e && e <= 1008 && e % 24 == 0)
      val xx = new Array[Double](5)
      val i0 = __HI(__LO(0.0d, __LO(x)), ix - (e << 20)) // math.scalb(x, -e)
      xx(0) = i0.toInt.toDouble
      val i1 = (i0 - xx(0)) * TWO24
      xx(1) = i1.toInt.toDouble
      val i2 = (i1 - xx(1)) * TWO24
      xx(2) = i2.toInt.toDouble
      val i3 = (i2 - xx(2)) * TWO24
      xx(3) = i3.toInt.toDouble
      val i4 = (i3 - xx(3)) * TWO24
      xx(4) = i4.toInt.toDouble
      (e, xx)
    }.ensuring(res =>
      24 <= res._1 && res._1 <= 1008 && res._1 % 24 == 0
        && xxInv(res._2)
    )

    /**
     * Multiply a double, represented using 24-bit chunks as `(e, xx)`, by two over pi.
     * For efficiency, parts of the result not relevant to the Payne-Hanek range reduction are not computed.
     * Modulo `2^24`, the result is computed within `2^-(24 * jz - 28)` of the real-valued result.
     * @param jz used to select precision of the result
     * @param e exponent of first bit-chunk of the input double
     * @param xx the 24-bit integer chunks of the input double
     * @return the result as an array of 51-bit integer chunks where the exponent at index `i` is `-24 * i`
     */
    @opaque @pure
    private def timesTwoOverPi(jz: Int, e: Int, xx: Array[Double]): Array[Double] = {
      require(0 <= jz && jz <= 15)
      require(24 <= e && e <= 1008 && e % 24 == 0)
      require(xxInv(xx))

      val jx = xx.length - 1
      val jv = {
        val tmp = (e - 3) / 24
        if tmp < 0 then 0 else tmp
      }
      val q0 = e - 24 * (jv + 1)
      assert(q0 == 0) // sanity check since the input splitting is not implemented exactly as in the original

      val f = new Array[Double](20)
      var i = 0
      (while (i <= jx + jz) {
        decreases(jx + jz + 1 - i)
        if jv - jx + i >= 0 then f(i) = two_over_pi(jv - jx + i).toDouble
        i += 1
      }).invariant(
        0 <= i && i <= jx + jz + 1
          && fInv(f)
      )

      val q = new Array[Double](20)
      i = 0
      (while (i <= jz) {
        decreases(jz + 1 - i)
        q(i) = xx(0) * f(i + 4) + xx(1) * f(i + 3) + xx(2) * f(i + 2) + xx(3) * f(i + 1) + xx(4) * f(i)
        assert(Q(f(i + 4)))
        assert(Q(f(i + 3)))
        assert(Q(f(i + 2)))
        assert(Q(f(i + 1)))
        assert(Q(f(i)))
        assert(P(q(i)))
        i += 1
      }).invariant(
        0 <= i && i <= jz + 1
          && fInv(f)
          && qInv(q)
      )

      // If it were computed, `q(jz + 1)` would be a 51-bit integer.
      // Hence, less than "28 bits" are missing from the computed part of `q`.
      // Thus, the result is computed within `2^-(24 * jz - 28)` of the real result, modulo 2^24.
      // (Carry terms from `q(jz + 2)`, `q(jz + 3)`, etc. should not affect this, see e.g. the bounds on `z` in `computeModulo()`.)
      q
    }.ensuring(res => qInv(res))

    /**
     * Compute `n` and `r` such that the input modulo `2 * pi` is `n * (pi / 4) + r`.
     * @param jz highest index of `q` containing part of the input
     * @param q input represented using 51-bit integer chunks where index `i` has exponent `-24 * i`
     * @return `(n, neg, oneHalf, qq)` where `qq` represents the absolute value of `r` using 24-bit chunks where
     *         index `i` has exponent `-24 * i`, `neg` is true iff `r` is negative, and `oneHalf` is true if `r == 0.5`.
     */
    @opaque @pure
    private def computeModulo(jz: Int, q: Array[Double]): (Int, Boolean, Boolean, Array[Double]) = {
      require(2 <= jz && jz < 19)
      require(qInv(q))

      val iq = new Array[Int](20)
      var j = jz
      var z = q(jz)
//      val fw0 = (twon24 * z).toInt.toDouble
//      iq(jz - j) = (z - TWO24 * fw0).toInt
//      assert(QInt(iq(jz - j)))
//      assert(0 <= fw0 && fw0 <= 0x500_0002)
//      assert(P(q(j - 1)))
//      z = q(j - 1) + fw0
//      j -= 1
//      val fw1 = (twon24 * z).toInt.toDouble
//      iq(jz - j) = (z - TWO24 * fw1).toInt
//      assert(QInt(iq(jz - j)))
//      assert(0 <= fw1 && fw1 <= 0x500_0004)
//      assert(P(q(j - 1)))
//      z = q(j - 1) + fw1
//      j -= 1
      (while (j > 0) {
        decreases(j)
        val fw = (twon24 * z).toInt.toDouble
        iq(jz - j) = (z - TWO24 * fw).toInt
        assert(QInt(iq(jz - j)))
        assert(0 <= fw && fw <= 0x500_0004)
        assert(P(q(j - 1)))
        z = q(j - 1) + fw
        j -= 1
      }).invariant(
        0 <= j && j <= jz
          && 0 <= z && z <= 5 * 0xffff_ffff_ffffL + 0x500_0004
          && iqInv(iq)
      )

      z -= 8.0d * (z * 0.125).toLong.toDouble
      assert(0 <= z && z < 8)
      val neg = iq(jz - 1) >= 0x80_0000
      val n = if neg then (z.toInt + 1) & 7 else z.toInt

      var carry = 0
      if (neg) {
        var i = 0
        (while (i < jz - 1) {
          decreases(jz - i)
          val j = iq(i)
          assert(QInt(j))
          iq(i) = if carry == 0 then if j != 0 then 0x100_0000 - j else 0 else 0xff_ffff - j
          carry = if carry == 0 && j != 0 then 1 else carry
          i += 1
        }).invariant(
          0 <= i && i <= jz - 1
            && iqInv(iq) && iq(jz - 1) >= 0x80_0000
            && (carry == 0 || carry == 1)
        )
        val j = iq(jz - 1)
        iq(jz - 1) = if carry == 0 then 0x100_0000 - j else 0xff_ffff - j
      }

      assert(0 <= iq(jz - 1) && iq(jz - 1) <= 0x80_0000)
      val oneHalf = neg && carry == 0 && iq(jz - 1) == 0x80_0000

      val qq = new Array[Double](20)
      assert(qqInv(qq))
      if (!oneHalf) {
        assert(iq(jz - 1) <= 0x7f_ffff)
        var i = 0
        (while (i < jz) {
          decreases(jz - i)
          assert(QInt(iq(jz - 1 - i)))
          qq(i) = twon24Pow(i + 1) * iq(jz - 1 - i)
          assert(0 <= qq(i) && qq(i) <= qqBound(i))
          assert(qq.length == 20 && qqInv(qq))
          i += 1
        }).invariant(
          0 <= i && i <= jz
            && iqInv(iq) && iq(jz - 1) <= 0x7f_ffff
            && qq.length == 20 && qqInv(qq)
        )
      }

      (n, neg, oneHalf, qq)
    }.ensuring(res =>
      0 <= res._1 && res._1 < 8
        && res._4.length == 20 && qqInv(res._4)
    )

    /**
     * Multiply the input by 120 bits of pi over two.
     * @param jz number of leading elements of `qq` containing part of the input
     * @param qq the input represented by 24-bit chunks
     * @return an array representing the result as an unevaluated sum
     */
    @opaque @pure
    private def timesPiOverTwo(jz: Int, qq: Array[Double]): Array[Double] = {
      require(0 <= jz && jz < 20)
      require(qq.length == 20 && qqInv(qq))
      val fq = new Array[Double](20)
      fq(0) = PIo2(0) * qq(0)
      assert(0 <= fq(0) && fq(0) <= fqBound(0))
      fq(1) = PIo2(0) * qq(1) + PIo2(1) * qq(0)
      assert(0 <= fq(1) && fq(1) <= fqBound(1))
      fq(2) = PIo2(0) * qq(2) + PIo2(1) * qq(1) + PIo2(2) * qq(0)
      assert(0 <= fq(2) && fq(2) <= fqBound(2))
      fq(3) = PIo2(0) * qq(3) + PIo2(1) * qq(2) + PIo2(2) * qq(1) + PIo2(3) * qq(0)
      assert(0 <= fq(3) && fq(3) <= fqBound(3))
      var i = 4
      (while (i < jz) {
        decreases(jz - i)
        val fw0 = PIo2(0) * qq(i - 0)
        val fw1 = PIo2(1) * qq(i - 1)
        val fw2 = PIo2(2) * qq(i - 2)
        val fw3 = PIo2(3) * qq(i - 3)
        val fw4 = PIo2(4) * qq(i - 4)
        val fw = fw0 + fw1 + fw2 + fw3 + fw4
        assert(0 <= fw0 && fw0 <= PIo2(0) * qqBound(i - 0))
        assert(0 <= fw1 && fw1 <= PIo2(1) * qqBound(i - 1))
        assert(0 <= fw2 && fw2 <= PIo2(2) * qqBound(i - 2))
        assert(0 <= fw3 && fw3 <= PIo2(3) * qqBound(i - 3))
        assert(0 <= fw4 && fw4 <= PIo2(4) * qqBound(i - 4))
        assert(0 <= fw && fw <= fqBound(i))
        fq(i) = fw
        i += 1
      }).invariant(
        4 <= i && i <= jz
          && qq.length == 20 && qqInv(qq)
          && fq.length == 20 && fqInv(fq)
      )
      fq
    }.ensuring(res =>
      res.length == 20 && fqInv(res)
    )

    private def fast2Sum(a: Double, b: Double): (Double, Double) = {
      require((a + b).isFinite)
      require((if a < 0 then -a else a) >= (if b < 0 then -b else b))
      val s = a + b
      (s, a - s + b)
    }.ensuring(res => res._1 + res._2 == res._1)

//    private def twoSum(a: Double, b: Double): (Double, Double) = {
//      require((a + b).isFinite)
//      require((2 * a).isFinite)
//      require((2 * b).isFinite)
//      val s = a + b
//      val a1 = s - b
//      val b1 = s - a1
//      val da = a - a1
//      val db = b - b1
//      val t = da + db
//      (s, t)
//    }.ensuring(res => res._1 + res._2 == res._1)

    /**
     * Compress the input to a double-double representation (a double plus a compensation term).
     * @param jz number of leading elements of `fq` containing part of the input
     * @param fq the input represented as an unevaluated sum
     * @param neg true iff the input is negative
     * @return the input represented as a double-double
     */
    @opaque @pure
    private def fqCompression(jz: Int, fq: Array[Double], neg: Boolean): (Double, Double) = {
      require(fq.length == 20 && fqInv(fq))
      require(0 <= jz && jz < 20)
      var s = 0.0d
      var c = 0.0d
      var i = jz - 1
      // Coincidentally, this seems to be very similar to the XBLAS sum algorithm.
      (while (i >= 0) {
        decreases(i + 1)
        assert(0 <= s && s <= 1)
        // twoSum could also be used here, but it adds ~1 hour to the verification time
        val (s1, c1) = if s >= fq(i) then fast2Sum(s, fq(i)) else fast2Sum(fq(i), s)
        assert(s1 >= c + c1)
        val (s2, c2) = fast2Sum(s1, c + c1)
        s = s2
        c = c2
        i -= 1
      }).invariant(
        -1 <= i && i <= jz - 1
          && 0 <= s && s <= sBound(i + 1) && s + c == s
          && fq.length == 20 && fqInv(fq)
      )
      if neg then (-s, -c) else (s, c)
    }.ensuring(res =>
      -0.7853981633974483 <= res._1 && res._1 <= 0.7853981633974483 && res._1 + res._2 == res._1
    )

    //// The range reduction algorithm ////

    /**
     * Compute `x mod pi / 2` using the Payne-Hanek method,
     * returning `y` in `[-pi / 4, pi / 4]` and `n` in `[0, 8)` such that `x == n * (pi / 4) + y` modulo `pi / 2`.
     * @param x finite double to compute modulo `pi / 2`
     * @return `(n, y0, y1)` where `y` is the unevaluated sum `y0 + y1`.
     */
    @opaque @pure
    def __kernel_rem_pio2(x: Double): (Int, Double, Double) = {
      require(1 <= x && x.isFinite)

      // Here, `x * (2 / pi) mod 1` is computed within `2^-(24 * jz - 28)` of the real-valued result.
      // The worst-case input, the double closest to a multiple of `pi / 2`, is `5.319372648326541E255`, for which
      // there is 61 "extra" leading zeros in `x * (2 / pi) mod 1` due to cancellation.
      // Hence, for correct rounding, we need to compute `x * (2 / pi) mod 1`
      // within `2^-(61 + (desired precision) + 1)` of the real-valued result.
      // Thus, `jz = 6` yields at least 54 "correct bits" of `x * (2 / pi) mod 1`, and `jz = 7` yields 78.
      //
      // In practice, a lower value of `jz` is often sufficient.
      // Empirically, for 10's of billions of random doubles, and all single precision numbers
      // using `jz = 5` was sufficient to compute `sin` and `cos` with 1 ulp of a reference implementation.
      // For `5.319372648326541E255` `sin` was computed within 1 ulp, but not `cos`.
      // For `jz = 4`, a 1 ulp result, compared to a reference implementation, was obtained for:
      // - `cos()` for 9999997353/10000000000 random doubles (all except 2647)
      // - `cos()` for all single precision numbers except 632
      // - `sin()` for 9999997427/10000000000 random doubles (all except 2573)
      // - `sin()` for all single precision numbers except 632
      // - `sin()` for the worst-case input (but not for `cos()`)
      // But, being within 1 ulp of a reference implementation does not necessarily imply being withing 1 ulp of the correct result.
      // A possible performance optimization is to use an adaptive number of bits of `2 / pi`.

      // TODO: test against OpenJDK's FdLibm implementation
      // TODO: proof might be faster if `jz` is moved to the object and removed as a parameter to the methods.

      val jz = 6
      val (e, xx) = splitInput(x)
      val q = timesTwoOverPi(jz, e, xx)
      val (n, neg, oneHalf, qq) = computeModulo(jz, q)
      if (oneHalf)
        // This case should be unreachable, assuming sufficient precision is used.
        // But, it is currently challenging to impossible to show this in stainless.
        // It is simpler to just treat `x * (2 / pi) mod 1 ~== 0.5` as a special case.
        (n, 0.7853981633974483d, 9.615660845819876E-18)
      else {
        val fq = timesPiOverTwo(jz, qq)
        val (y0, y1) = fqCompression(jz, fq, neg)
        (n, y0, y1)
      }
    }.ensuring(res =>
      0 <= res._1 && res._1 < 8
        && -0.7853981633974483d <= res._2 && res._2 <= 0.7853981633974483d
        && res._2 + res._3 == res._2
    )

    //// rewrite of range reduction algorithm into a single function ////

    /**
     * Compute `x mod pi / 2` using the Payne-Hanek method,
     * returning `y` in `[-pi / 4, pi / 4]` and `n` in `[0, 8)` such that `x == n * (pi / 4) + y` modulo `pi / 2`.
     *
     * @param x finite double to compute modulo `pi / 2`
     * @return `(n, y0, y1)` where `y` is the unevaluated sum `y0 + y1`.
     */
    @opaque @pure
    def __kernel_rem_pio2_inlined(x: Double): (Int, Double, Double) = {
      require(1 <= x && x.isFinite)
      // It takes a very long time to show some preconditions in this function, extra assertions are required;
      // and, we get a stack overflow in Stainless after showing these pre-conditions :)

      // Here, `x * (2 / pi) mod 1` is computed within `2^-(24 * jz - 28)` of the real-valued result.
      // The worst-case input, the double closest to a multiple of `pi / 2`, is `5.319372648326541E255`, for which
      // there is 61 "extra" leading zeros in `x * (2 / pi) mod 1` due to cancellation.
      // Hence, for correct rounding, we need to compute `x * (2 / pi) mod 1`
      // within `2^-(61 + (desired precision) + 1)` of the real-valued result.
      // Thus, `jz = 6` yields at least 54 "correct bits" of `x * (2 / pi) mod 1`, and `jz = 7` yields 78.
      //
      // In practice, a lower value of `jz` is often sufficient.
      // Empirically, for 10's of billions of random doubles, and all single precision numbers
      // using `jz = 5` was sufficient to compute `sin` and `cos` with 1 ulp of a reference implementation.
      // For `5.319372648326541E255` `sin` was computed within 1 ulp, but not `cos`.
      // For `jz = 4`, a 1 ulp result, compared to a reference implementation, was obtained for:
      // - `cos()` for 9999997353/10000000000 random doubles (all except 2647)
      // - `cos()` for all single precision numbers except 632
      // - `sin()` for 9999997427/10000000000 random doubles (all except 2573)
      // - `sin()` for all single precision numbers except 632
      // - `sin()` for the worst-case input (but not for `cos()`)
      // But, being within 1 ulp of a reference implementation does not necessarily imply being withing 1 ulp of the correct result.
      // A possible performance optimization is to use an adaptive number of bits of `2 / pi`.

      // TODO: test against OpenJDK's FdLibm implementation

      val jz = 6

      // Step 1:
      // Split the input `x` into an array of 24-bit integer chunks, represented using doubles.
      // Leading zeros may be inserted to ensure the exponents of the chunks are multiples of `24`.
      // After splitting, `e % 24 == 0` and `x == (for (i <- 0 to 4) yield xx[i] * math.scalb(1.0d, e - 24 * i)).sum`. TODO: test

      val hx = __HI(x)
      val ix = hx & EXP_SIGNIF_BITS
      val e0 = (ix >> 20) - 1046 // exponent - 23
      assert(-23 <= e0 && e0 <= 1000)
      val e = {
        val tmp = 24 * ((e0 + 23) / 24)
        if tmp < 24 then 24 else tmp
      }
      assert(24 <= e && e <= 1008 && e % 24 == 0)
      val xx = new Array[Double](5)
      val i0 = __HI(__LO(0.0d, __LO(x)), ix - (e << 20)) // math.scalb(x, -e)
      xx(0) = i0.toInt.toDouble
      val i1 = (i0 - xx(0)) * TWO24
      xx(1) = i1.toInt.toDouble
      val i2 = (i1 - xx(1)) * TWO24
      xx(2) = i2.toInt.toDouble
      val i3 = (i2 - xx(2)) * TWO24
      xx(3) = i3.toInt.toDouble
      val i4 = (i3 - xx(3)) * TWO24
      xx(4) = i4.toInt.toDouble

      // Step 2:
      // Multiply the double, represented using 24-bit chunks as `(e, xx)`, by two over pi.
      // For efficiency, parts of the result not relevant to the Payne-Hanek range reduction are not computed.
      // Modulo `2^24`, the result is computed within `2^-(24 * jz - 28)` of the real-valued result.
      // The result is stored in the array `q` consisting of 51-bit integer chunks where the exponent at index `i` is `-24 * i`.

      val jx = xx.length - 1
      val jv = {
        val tmp = (e - 3) / 24
        if tmp < 0 then 0 else tmp
      }
      val q0 = e - 24 * (jv + 1)
      assert(q0 == 0) // sanity check since the input splitting is not implemented exactly as in the original

      val f = new Array[Double](20)
      var i = 0
      (while (i <= jx + jz) {
        decreases(jx + jz + 1 - i)
        if jv - jx + i >= 0 then f(i) = two_over_pi(jv - jx + i).toDouble
        i += 1
      }).invariant(
        0 <= i && i <= jx + jz + 1
          && xxInv(xx) && fInv(f)
      )

      val q = new Array[Double](20)
      assert(fInv(f)) // pre-condition/invariant takes an insanely long time to show without these assertions
      assert(qInv(q))
      i = 0
      (while (i <= jz) {
        decreases(jz + 1 - i)
        q(i) = xx(0) * f(i + 4) + xx(1) * f(i + 3) + xx(2) * f(i + 2) + xx(3) * f(i + 1) + xx(4) * f(i)
        assert(Q(f(i + 4)))
        assert(Q(f(i + 3)))
        assert(Q(f(i + 2)))
        assert(Q(f(i + 1)))
        assert(Q(f(i)))
        assert(P(q(i)))
        i += 1
      }).invariant(
        0 <= i && i <= jz + 1
          && fInv(f)
          && qInv(q)
      )

      // Step 3:
      // Compute `n` and `r` such that the input modulo `2 * pi` is `n * (pi / 4) + r`.
      // The result consists of `(n, neg, oneHalf, qq)` where `qq` represents the absolute value of `r` using 24-bit chunks
      // where index `i` has exponent `-24 * i`, `neg` is true iff `r` is negative, and `oneHalf` is true if `r == 0.5`.

      val iq = new Array[Int](20)
      var j = jz
      var z = q(jz)
      //      val fw0 = (twon24 * z).toInt.toDouble
      //      iq(jz - j) = (z - TWO24 * fw0).toInt
      //      assert(QInt(iq(jz - j)))
      //      assert(0 <= fw0 && fw0 <= 0x500_0002)
      //      assert(P(q(j - 1)))
      //      z = q(j - 1) + fw0
      //      j -= 1
      //      val fw1 = (twon24 * z).toInt.toDouble
      //      iq(jz - j) = (z - TWO24 * fw1).toInt
      //      assert(QInt(iq(jz - j)))
      //      assert(0 <= fw1 && fw1 <= 0x500_0004)
      //      assert(P(q(j - 1)))
      //      z = q(j - 1) + fw1
      //      j -= 1
      assert(qInv(q)) // pre-condition/invariant takes an insanely long time to show without these assertions
      assert(iqInv(iq))
      assert(0 <= z && z <= 5 * 0xffff_ffff_ffffL)
      (while (j > 0) {
        decreases(j)
        val fw = (twon24 * z).toInt.toDouble
        iq(jz - j) = (z - TWO24 * fw).toInt
        assert(QInt(iq(jz - j)))
        assert(0 <= fw && fw <= 0x500_0004)
        assert(P(q(j - 1)))
        z = q(j - 1) + fw
        j -= 1
      }).invariant(
      0 <= j && j <= jz
        && 0 <= z && z <= 5 * 0xffff_ffff_ffffL + 0x500_0004
        && qInv(q) && iqInv(iq)
      )

      // If it were computed, `q(jz + 1)` would be a 51-bit integer.
      // Hence, less than "28 bits" are missing from the computed part of `q`.
      // Thus, the result is computed within `2^-(24 * jz - 28)` of the real result, modulo 2^24.
      // (Carry terms from `q(jz + 2)`, `q(jz + 3)`, etc. should not affect this, see e.g. the bounds on `z` below.)

      z -= 8.0d * (z * 0.125).toLong.toDouble
      assert(0 <= z && z < 8)
      val neg = iq(jz - 1) >= 0x80_0000
      val n = if neg then (z.toInt + 1) & 7 else z.toInt

      var carry = 0
      if (neg) {
        assert(iqInv(iq) && iq(jz - 1) >= 0x80_0000) // pre-condition/invariant takes an insanely long time to show without these assertions
        var i = 0
        (while (i < jz - 1) {
          decreases(jz - i)
          val j = iq(i)
          assert(QInt(j))
          iq(i) = if carry == 0 then if j != 0 then 0x100_0000 - j else 0 else 0xff_ffff - j
          carry = if carry == 0 && j != 0 then 1 else carry
          i += 1
        }).invariant(
          0 <= i && i <= jz - 1
            && iqInv(iq) && iq(jz - 1) >= 0x80_0000
            && (carry == 0 || carry == 1)
        )
        val j = iq(jz - 1)
        iq(jz - 1) = if carry == 0 then 0x100_0000 - j else 0xff_ffff - j
      }

      assert(0 <= iq(jz - 1) && iq(jz - 1) <= 0x80_0000)
      val oneHalf = neg && carry == 0 && iq(jz - 1) == 0x80_0000

      val qq = new Array[Double](20)
      if (!oneHalf) {
        var i = 0
        assert(iqInv(iq)) // pre-condition/invariant takes an insanely long time to show without these assertions
        assert(qqInv(qq))
        (while (i < jz) {
          decreases(jz - i)
          assert(QInt(iq(jz - 1 - i)))
          qq(i) = twon24Pow(i + 1) * iq(jz - 1 - i)
          assert(0 <= qq(i) && qq(i) <= qqBound(i))
          assert(qqInv(qq))
          i += 1
        }).invariant(
          0 <= i && i <= jz
            && iqInv(iq) && iq(jz - 1) <= 0x7f_ffff
            && qqInv(qq)
        )
      }

      if (oneHalf)
        // This case should be unreachable, assuming sufficient precision is used.
        // But, it is currently challenging to impossible to show this in stainless.
        // It is simpler to just treat `x * (2 / pi) mod 1 ~== 0.5` as a special case.
        (n, 0.7853981633974483d, 9.615660845819876E-18)
      else {
        // Step 4:
        // Multiply the `r` (stored in `qq`) by 120 bits of pi over two.
        // The result is stored in the array `fq` as an unevaluated sum.
        val fq = new Array[Double](20)
        fq(0) = PIo2(0) * qq(0)
        assert(0 <= fq(0) && fq(0) <= fqBound(0))
        fq(1) = PIo2(0) * qq(1) + PIo2(1) * qq(0)
        assert(0 <= fq(1) && fq(1) <= fqBound(1))
        fq(2) = PIo2(0) * qq(2) + PIo2(1) * qq(1) + PIo2(2) * qq(0)
        assert(0 <= fq(2) && fq(2) <= fqBound(2))
        fq(3) = PIo2(0) * qq(3) + PIo2(1) * qq(2) + PIo2(2) * qq(1) + PIo2(3) * qq(0)
        assert(0 <= fq(3) && fq(3) <= fqBound(3))
        var i = 4
        (while (i < jz) {
          decreases(jz - i)
          val fw0 = PIo2(0) * qq(i - 0)
          val fw1 = PIo2(1) * qq(i - 1)
          val fw2 = PIo2(2) * qq(i - 2)
          val fw3 = PIo2(3) * qq(i - 3)
          val fw4 = PIo2(4) * qq(i - 4)
          val fw = fw0 + fw1 + fw2 + fw3 + fw4
          assert(0 <= fw0 && fw0 <= PIo2(0) * qqBound(i - 0))
          assert(0 <= fw1 && fw1 <= PIo2(1) * qqBound(i - 1))
          assert(0 <= fw2 && fw2 <= PIo2(2) * qqBound(i - 2))
          assert(0 <= fw3 && fw3 <= PIo2(3) * qqBound(i - 3))
          assert(0 <= fw4 && fw4 <= PIo2(4) * qqBound(i - 4))
          assert(0 <= fw && fw <= fqBound(i))
          fq(i) = fw
          i += 1
        }).invariant(
          4 <= i && i <= jz
            && qqInv(qq) && fqInv(fq)
        )

        // Step 5:
        // Compress the input to a double-double representation (a double plus a compensation term).
        var s = 0.0d
        var c = 0.0d
        var j = jz - 1
        // Coincidentally, this seems to be very similar to the XBLAS sum algorithm.
        assert(fqInv(fq))
        (while (j >= 0) {
          decreases(j + 1)
          assert(0 <= s && s <= 1)
          // twoSum could also be used here, but it adds ~1 hour to the verification time
          val (s1, c1) = if s >= fq(j) then fast2Sum(s, fq(j)) else fast2Sum(fq(j), s)
          assert(s1 >= c + c1)
          val (s2, c2) = fast2Sum(s1, c + c1)
          s = s2
          c = c2
          j -= 1
        }).invariant(
        -1 <= j && j <= jz - 1
          && 0 <= s && s <= sBound(i + 1) && s + c == s
          && fqInv(fq)
        )
        val (y0, y1) = if neg then (-s, -c) else (s, c)
        (n, y0, y1)
      }
    }.ensuring(res =>
      0 <= res._1 && res._1 < 8
        && -0.7853981633974483d <= res._2 && res._2 <= 0.7853981633974483d
        && res._2 + res._3 == res._2
    )
  }

  // TODO: test
  object ASin {

    @extern @pure
    private def assume(P: Boolean): Unit = {}.ensuring(P)

    def asin(x: Double): Double = {
      val hx = __HI(x)
      val ix = hx & EXP_SIGNIF_BITS
      if (ix >= 0x3ff0_0000) { // |x| >= 1
        if (((ix - 0x3ff0_0000) | __LO(x)) == 0) // |x| == 1
          x * pio2_hi + x * pio2_lo
        else
          (x - x) / (x - x) // return NaN
      }
      else if (ix < 0x3fe0_0000) { // |x| < 0.5
        if (ix < 0x3e40_0000 && huge + x > 1.0) // |x| < 0x1p-27 && x != 0
          x
        else {
          val t = if ix < 0x3e40_0000 then x * x else 0 // if |x| < 0x1p-27
          val w = R(t)
          x + x * w
        }
      }
      else {
        val w = 1.0 - (if x > 0.0d then x else -x)
//        assert(0.0d <= w && w <= 0.5d)
        val t = w * 0.5
//        assert(0.0d <= t && t <= 0.25d)
        val s = math.sqrt(t)
//        assert(0.0d <= s && s <= 0.5d)
        val t2 = if (ix >= 0x3fef_3333) { // |x| >= 0.974999904632568359375
          val w = R(t)
          assert(0.0d <= w)
          assert(w <= 0.5707963267948966d)
          pio2_hi - (2.0d * (s + s * w) - pio2_lo)
        } else {
          val w = __LO(s, 0)
          assert(0.0d <= w && w <= s && s <= 0.5d)
//          assert(w * w <= s * s)
//          assert(s * s <= t + 1.1102230246251565E-16)
//          assert(w * w <= t + 1.1102230246251565E-16)
//          assert(0.0d < s * w)
          val c = (t - w * w) / (s * w)
//          assume(-1e10 <= c && c <= 1e10)
          val r = R(t)
          assert(-1E-10 <= c && c <= 1E-10) // TIMEOUT with 100s // TIMEOUT with 1000s
          assert(0.0d <= s * r)
          val p2 = 2.0 * s * r - (pio2_lo - 2.0 * c)
          assert(-pio2_lo <= p2) // TIMEOUT with 100s // TIMEOUT with 1000s
          val q2 = pio4_hi - 2.0 * w
          assert(q2 <= pio4_hi)
          assert(0.0d <= pio4_hi - (p2 - q2))
          assert(pio4_hi - (p2 - q2) <= 1.5707963267948966d) // TIMEOUT with 100s
          pio4_hi - (p2 - q2)
        }
        assert(ix < 0x3fef_3333 || 0 <= t2 && t2 <= 1.5707963267948966d)
        assert(ix >= 0x3fef_3333 || 0 <= t2 && t2 <= 1.5707963267948966d) // TIMEOUT with 100s // TIMEOUT with 1000s
        if hx > 0 then t2 else -t2 // TIMEOUT with 100s // TIMEOUT with 1000s
      }
    }.ensuring(res =>
      (!(x.isNaN || x < -1.0d || x > 1.0d) || res.isNaN)
        && x.equiv(+0.0d) == res.equiv(+0.0d)
        && x.equiv(-0.0d) == res.equiv(-0.0d)
        && (!(-1.0d <= x && x <= 1.0d) || (-1.5707963267948966d <= res && res <= 1.5707963267948966d))
    )

    private def R(z: Double): Double = {
      require(0.0d <= z && z <= 0.5d)
      val p = z * (pS0 + z * (pS1 + z * (pS2 + z * (pS3 + z * (pS4 + z * pS5)))))
      assert(0.0d <= p && p <= 0.025)
      val q = 1.0d + z * (qS1 + z * (qS2 + z * (qS3 + z * qS4)))
      assert(0.5 <= q && q <= 1.0d)
      p / q
    }.ensuring(res => 0 <= res && res <= 0.05d)

    private val huge = 1e300d
    private val pio2_hi = 1.57079632679489655800e+00 // 0x1.921fb54442d18p0,
    private val pio2_lo = 6.12323399573676603587e-17 // 0x1.1a62633145c07p-54,
    private val pio4_hi = 7.85398163397448278999e-01 // 0x1.921fb54442d18p-1,
    private val pS0 =  1.66666666666666657415e-01 //   0x1.5555555555555p-3,
    private val pS1 = -3.25565818622400915405e-01 //  -0x1.4d61203eb6f7dp-2,
    private val pS2 =  2.01212532134862925881e-01 //   0x1.9c1550e884455p-3,
    private val pS3 = -4.00555345006794114027e-02 //  -0x1.48228b5688f3bp-5,
    private val pS4 =  7.91534994289814532176e-04 //   0x1.9efe07501b288p-11
    private val pS5 =  3.47933107596021167570e-05 //   0x1.23de10dfdf709p-15
    private val qS1 = -2.40339491173441421878e+00 //  -0x1.33a271c8a2d4bp1,
    private val qS2 =  2.02094576023350569471e+00 //   0x1.02ae59c598ac8p1,
    private val qS3 = -6.88283971605453293030e-01 //  -0x1.6066c1b8d0159p-1,
    private val qS4 =  7.70381505559019352791e-02 //   0x1.3b8c5b12e9282p-4;
  }

  // TODO: test
  object ACos {
    def acos(x: Double): Double = {
      val hx = __HI(x)
      val ix = hx & EXP_SIGNIF_BITS
      if (ix >= 0x3ff0_0000) {
        if (((ix - 0x3ff0_0000) | __LO(x)) == 0)
          if hx > 0 then 0.0 else Math.PI + 2.0 * pio2_lo
        else
          (x - x) / (x - x)
      }
      else if (ix < 0x3fe0_0000) {
        if (ix <= 0x3fe0_0000)
          pio2_hi + pio2_lo
        else {
          val z = x * x
          val r = R(z)
          pio2_hi - (x - (pio2_lo - x * r))
        }
      }
      else if (hx < 0) {
        val z = (1.0d + x) * 0.5
        val s = math.sqrt(z)
        val r = R(z)
        val w = r * s - pio2_lo
        Math.PI - 2.0 * (s + w)
      }
      else {
        assert(0.5d <= x && x <= 1.0d)
        val z = (1.0d - x) * 0.5
        val s = math.sqrt(z)
        val df = __LO(s, 0)
        assert(0.0d <= df && df <= s && s <= 0.7071067811865476d)
        val c = (z - df * df) / (s + df)
        assert(-1e10 <= c && c <= 1e10) // Why does this assertion make the assertion below provable in a reasonable amount of time???
        assert(0.0d <= df + c)
        val r = R(z)
        val w = r * s + c
        assert(c <= w)
        2.0 * (df + w) // TIMEOUT with 100s
      }
    }.ensuring(res =>
      (!(x.isNaN || x < -1.0d || x > 1.0d) || res.isNaN)
        && (!(-1.0d <= x && x <= 1.0d) || (0 <= res && res <= 3.14159265358979323846d))
    )

    private def R(z: Double): Double = {
      require(0.0d <= z && z <= 0.5d)
      val p = z * (pS0 + z * (pS1 + z * (pS2 + z * (pS3 + z * (pS4 + z * pS5)))))
      assert(0.0d <= p && p <= 0.025)
      val q = 1.0d + z * (qS1 + z * (qS2 + z * (qS3 + z * qS4)))
      assert(0.5 <= q && q <= 1.0d)
      p / q
    }.ensuring(res => 0 <= res && res <= 0.05d)

    private val pio2_hi = 1.57079632679489655800e+00 //  0x1.921fb54442d18p0,
    private val pio2_lo = 6.12323399573676603587e-17 //  0x1.1a62633145c07p-54,
    private val pS0 =  1.66666666666666657415e-01 //  0x1.5555555555555p-3,
    private val pS1 = -3.25565818622400915405e-01 // -0x1.4d61203eb6f7dp-2,
    private val pS2 =  2.01212532134862925881e-01 //  0x1.9c1550e884455p-3,
    private val pS3 = -4.00555345006794114027e-02 // -0x1.48228b5688f3bp-5,
    private val pS4 =  7.91534994289814532176e-04 //  0x1.9efe07501b288p-11,
    private val pS5 =  3.47933107596021167570e-05 //  0x1.23de10dfdf709p-15,
    private val qS1 = -2.40339491173441421878e+00 // -0x1.33a271c8a2d4bp1
    private val qS2 =  2.02094576023350569471e+00 //  0x1.02ae59c598ac8p1
    private val qS3 = -6.88283971605453293030e-01 // -0x1.6066c1b8d0159p-1
    private val qS4 =  7.70381505559019352791e-02 //  0x1.3b8c5b12e9282p-4
  }

  @ignore
  def testSin(): Unit = {
    var errors = 0
    val r = scala.util.Random
    r.setSeed(123)
    var j: Long = 0
    var i: Long = Int.MinValue
    val s1 = Sin.sin(5.319372648326541E255)
    val s2 = Math.sin(5.319372648326541E255)
    val diff = Math.abs(s1 - s2)
    val ulp = Math.min(Math.ulp(s1), Math.ulp(s2))
    if diff > ulp then {
//      println(s"[sin] error: d = worst-case, diff = $diff, s1 = $s1, s2 = $s2, ulp(s1) = ${Math.ulp(s1)}, ulp(s2r) = ${Math.ulp(s2)}")
//      j = 10000000000L + 1
//      i = Int.MaxValue.toLong + 1
      errors += 1
    }
    println(s"[sin] errors, worst-case: $errors")
    errors = 0
    while (j <= 10000000000L) {
      val d = java.lang.Double.longBitsToDouble(r.nextLong())
      if (j % 10000000 == 0)
        println(s"[sin] progress: $j")
      val s1 = Sin.sin(d)
      val s2 = Math.sin(d)
      val diff = Math.abs(s1 - s2)
      val ulp = Math.min(Math.ulp(s1), Math.ulp(s2))
      if diff > ulp then {
//        println(s"[sin] error: d = $d, diff = $diff, s1 = $s1, s2 = $s2, ulp(s1) = ${Math.ulp(s1)}, ulp(s2r) = ${Math.ulp(s2)}")
//        j = 10000000000L + 1
//        i = Int.MaxValue.toLong + 1
        errors += 1
      }
      j += 1
    }
    println(s"[sin] errors, random doubles: $errors")
    errors = 0
    while (i <= Int.MaxValue) {
      val d = java.lang.Float.intBitsToFloat(i.toInt).toDouble
      if (i % 100000000 == 0)
        println(s"[sin] progress: $d")
      val s1 = Sin.sin(d)
      val s2 = Math.sin(d)
      val diff = Math.abs(s1 - s2)
      val ulp = Math.min(Math.ulp(s1), Math.ulp(s2))
      if diff > ulp  then {
//        println(s"[sin] error: d = $d, diff = $diff, s1 = $s1, s2 = $s2, ulp(s1) = ${Math.ulp(s1)}, ulp(s2r) = ${Math.ulp(s2)}")
//        i = Int.MaxValue.toLong + 1
        errors += 1
      }
      i += 1
    }
    println(s"[sin] errors, singles: $errors")
  }

  @ignore
  def testCos(): Unit = {
    var errors: Long = 0
    val r = scala.util.Random
    r.setSeed(123)
    var j: Long = 0
    var i: Long = Int.MinValue
    val s1 = Cos.cos(5.319372648326541E255)
    val s2 = Math.cos(5.319372648326541E255)
    val diff = Math.abs(s1 - s2)
    val ulp = Math.min(Math.ulp(s1), Math.ulp(s2))
    if diff > ulp then {
//      println(s"[cos] error: d = worst-case, diff = $diff, s1 = $s1, s2 = $s2, ulp(s1) = ${Math.ulp(s1)}, ulp(s2r) = ${Math.ulp(s2)}")
//      j = 10000000000L + 1
//      i = Int.MaxValue.toLong + 1
      errors += 1
    }
    println(s"[cos] errors, worst-case: $errors")
    errors = 0
    while (j <= 10000000000L) {
      val d = java.lang.Double.longBitsToDouble(r.nextLong())
      if (j % 10000000 == 0)
        println(s"[cos] progress: $j")
      val s1 = Cos.cos(d)
      val s2 = Math.cos(d)
      val diff = Math.abs(s1 - s2)
      val ulp = Math.min(Math.ulp(s1), Math.ulp(s2))
      if diff > ulp then {
//        println(s"[cos] error: d = $d, diff = $diff, s1 = $s1, s2 = $s2, ulp(s1) = ${Math.ulp(s1)}, ulp(s2r) = ${Math.ulp(s2)}")
//        j = 10000000000L + 1
//        i = Int.MaxValue.toLong + 1
        errors += 1
      }
      j += 1
    }
    println(s"[cos] errors, random doubles: $errors")
    errors = 0
    while (i <= Int.MaxValue) {
      val d = java.lang.Float.intBitsToFloat(i.toInt).toDouble
      if (i % 100000000 == 0)
        println(s"[cos] progress: $d")
      val s1 = Cos.cos(d)
      val s2 = Math.cos(d)
      val diff = Math.abs(s1 - s2)
      val ulp = Math.min(Math.ulp(s1), Math.ulp(s2))
      if diff > ulp then {
//        println(s"[cos] error: d = $d, diff = $diff, s1 = $s1, s2 = $s2, ulp(s1) = ${Math.ulp(s1)}, ulp(s2r) = ${Math.ulp(s2)}")
//        i = Int.MaxValue.toLong + 1
        errors += 1
      }
      i += 1
    }
    println(s"[cos] errors, singles: $errors")
  }

  @ignore
  def main(argv: Array[String]): Unit = {testCos(); testSin()}
}
