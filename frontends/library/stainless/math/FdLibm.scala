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

    //// Old Stuff ////

    //    @opaque @pure
    //    private def fqCompression(fq: Array[Double], neg: Boolean): (Double, Double) = {
    //      require(fq.length == 20 && fqInv(fq))
    //      val fw0 = fq(19) + fq(18) + fq(17) + fq(16) + fq(15) + fq(14) + fq(13) + fq(12) + fq(11) + fq(10) + fq(9) + fq(8) + fq(7) + fq(6) + fq(5) + fq(4) + fq(3) + fq(2) + fq(1) + fq(0)
    //      assert(0 <= fw0 && fw0 <= 0.7853981633974483d) // math.Pi / 4 == 0.7853981633974483d
    ////      assert(-1.0000000002328306 * 1.3137570234753214E-7 <= fq(0) - fw0)
    ////      assert(-1.0000000001164153 * 1.3137570234753214E-7 <  = fq(0) - fw0) // INVALID
    //      val y0 = if neg then -fw0 else fw0
    //      val fw1 = fq(0) - fw0 + fq(1) + fq(2) + fq(3) + fq(4) + fq(5) + fq(6) + fq(7) + fq(8) + fq(9) + fq(10) + fq(11) + fq(12) + fq(13) + fq(14) + fq(15) + fq(16) + fq(17) + fq(18) + fq(19)
    ////      assert(0 <= fw0 + fw1 && fw0 + fw1 <= 0.7853981633974483d)
    ////      assert(-0.006135988326207402 - 6.418478184603245e-17 <= fw1 && fw1 <= 2.1792667318764053E-19 + 6.418478184603245e-17)
    //      assert(-1.3137570234753214E-7d / 32 <= fw1) // TODO: find tighter bound
    //      assert(fw1 <= 1.3137570234753214E-7d / 32)  // TODO: find tighter bound
    //      val y1 = if neg then -fw1 else fw1
    //      assume(y1 <= 1.1102230246251565E-16)
    //      (y0, y1)
    //    }.ensuring(res =>
    //      -0.7853981633974483d <= res._1 && res._1 <= 0.7853981633974483d
    //        && -1.3137570234753214E-7d / 32 <= res._2 && res._2 <= 1.3137570234753214E-7d / 32
    //    )

    @ignore @pure
    private def loop4Inv(a: Array[Double]): Boolean = {
      0 <= a(0) && a(0) <= 1.12589983973376E15 // 6.7108864E7 * 0xff_ffff
        && 0 <= a(1) && a(1) <= 6.710886E7 // 6.7108864E7 * twon24 * 0xff_ffff
        && 0 <= a(2) && a(2) <= 3.999999761581421 // 6.7108864E7 * twon24 * twon24 * 0xff_ffff
        && 0 <= a(3) && a(3) <= 2.3841856489070778E-7 // 6.7108864E7 * twon24 * ... * twon24 * 0xff_ffff
        && 0 <= a(4) && a(4) <= 1.4210853868169056E-14
        && 0 <= a(5) && a(5) <= 8.470328967672024E-22
        && 0 <= a(6) && a(6) <= 5.048709492487922E-29
        && 0 <= a(7) && a(7) <= 3.0092653587388526E-36
        && 0 <= a(8) && a(8) <= 1.7936619274251774E-43
        && 0 <= a(9) && a(9) <= 1.0691058203132018E-50
        && 0 <= a(10) && a(10) <= 6.372367264707099E-58
        && 0 <= a(11) && a(11) <= 3.7982268719119425E-65
        && 0 <= a(12) && a(12) <= 2.2639196347665444E-72
        && 0 <= a(13) && a(13) <= 1.3494012563029196E-79
        && 0 <= a(14) && a(14) <= 8.0430582541401365E-87
        && 0 <= a(15) && a(15) <= 4.7940363014579633E-94
        && 0 <= a(16) && a(16) <= 2.857468307887294E-101
        && 0 <= a(17) && a(17) <= 1.7031838344855868E-108
        && 0 <= a(18) && a(18) <= 1.015176674417011E-115
        && 0 <= a(19) && a(19) <= 6.0509245062888325E-123
    }

    @ignore @pure
    private def loop4InvNew(a: Array[Double]): Boolean = {
      0 <= a(0) && a(0) <= 0.5 // scalb(1.0, q0) * scalb(z2, -q0) where 0 <= z2 <= 0.5
        && 0 <= a(1) && a(1) <= 0.9999999403953552 // scalb(1.0, q0) * twon24 * (0xff_ffff when q0 <=0; 0x7f_ffff when q0 == 1; 0x3f_ffff when q0 == 2)
        && 0 <= a(2) && a(2) <= 2.3841856489070778E-7 // scalb(1.0, 2) * twon24 * twon24 * 0xff_ffff
        && 0 <= a(3) && a(3) <= 1.4210853868169056E-14 // scalb(1.0, 2) * twon24 * ... * twon24 * 0xff_ffff
        && 0 <= a(4) && a(4) <= 8.470328967672024E-22
        && 0 <= a(5) && a(5) <= 5.048709492487922E-29
        && 0 <= a(6) && a(6) <= 3.0092653587388526E-36
        && 0 <= a(7) && a(7) <= 1.7936619274251774E-43
        && 0 <= a(8) && a(8) <= 1.0691058203132018E-50
        && 0 <= a(9) && a(9) <= 6.372367264707099E-58
        && 0 <= a(10) && a(10) <= 3.7982268719119425E-65
        && 0 <= a(11) && a(11) <= 2.2639196347665444E-72
        && 0 <= a(12) && a(12) <= 1.3494012563029196E-79
        && 0 <= a(13) && a(13) <= 8.0430582541401365E-87
        && 0 <= a(14) && a(14) <= 4.7940363014579633E-94
        && 0 <= a(15) && a(15) <= 2.857468307887294E-101
        && 0 <= a(16) && a(16) <= 1.7031838344855868E-108
        && 0 <= a(17) && a(17) <= 1.015176674417011E-115
        && 0 <= a(18) && a(18) <= 6.0509245062888325E-123
        && 0 <= a(19) && a(19) <= 3.6066320576005176E-130
    }

    @ignore @pure
    private def loop4InvNew2(a: Array[Double], q0: Int): Boolean = {
      if (q0 == 2) {
        a(0) == 0
          && 0 <= a(1) && a(1) <= 0.4999997615814209
          && 0 <= a(2) && a(2) <= 2.3841856489070778E-7
          && 0 <= a(3) && a(3) <= 1.4210853868169056E-14
          && 0 <= a(4) && a(4) <= 8.470328967672024E-22
          && 0 <= a(5) && a(5) <= 5.048709492487922E-29
          && 0 <= a(6) && a(6) <= 3.0092653587388526E-36
          && 0 <= a(7) && a(7) <= 1.7936619274251774E-43
          && 0 <= a(8) && a(8) <= 1.0691058203132018E-50
          && 0 <= a(9) && a(9) <= 6.372367264707099E-58
          && 0 <= a(10) && a(10) <= 3.7982268719119425E-65
          && 0 <= a(11) && a(11) <= 2.2639196347665444E-72
          && 0 <= a(12) && a(12) <= 1.3494012563029196E-79
          && 0 <= a(13) && a(13) <= 8.0430582541401365E-87
          && 0 <= a(14) && a(14) <= 4.7940363014579633E-94
          && 0 <= a(15) && a(15) <= 2.857468307887294E-101
          && 0 <= a(16) && a(16) <= 1.7031838344855868E-108
          && 0 <= a(17) && a(17) <= 1.015176674417011E-115
          && 0 <= a(18) && a(18) <= 6.0509245062888325E-123
          && 0 <= a(19) && a(19) <= 3.6066320576005176E-130
      }
      else if (q0 == 1) {
        a(0) == 0
          && 0 <= a(1) && a(1) <= 0.49999988079071045
          && 0 <= a(2) && a(2) <= 1.1920928244535389E-7
          && 0 <= a(3) && a(3) <= 7.105426934084528E-15
          && 0 <= a(4) && a(4) <= 4.235164483836012E-22
          && 0 <= a(5) && a(5) <= 2.524354746243961E-29
          && 0 <= a(6) && a(6) <= 1.5046326793694263E-36
          && 0 <= a(7) && a(7) <= 8.968309637125887E-44
          && 0 <= a(8) && a(8) <= 5.345529101566009E-51
          && 0 <= a(9) && a(9) <= 3.1861836323535496E-58
          && 0 <= a(10) && a(10) <= 1.8991134359559713E-65
          && 0 <= a(11) && a(11) <= 1.1319598173832722E-72
          && 0 <= a(12) && a(12) <= 6.747006281514598E-80
          && 0 <= a(13) && a(13) <= 4.0215291270700682E-87
          && 0 <= a(14) && a(14) <= 2.3970181507289816E-94
          && 0 <= a(15) && a(15) <= 1.428734153943647E-101
          && 0 <= a(16) && a(16) <= 8.515919172427934E-109
          && 0 <= a(17) && a(17) <= 5.075883372085055E-116
          && 0 <= a(18) && a(18) <= 3.0254622531444163E-123
          && 0 <= a(19) && a(19) <= 1.8033160288002588E-130
      } else if (q0 == 0) {
        a(0) == 0
          && 0 <= a(1) && a(1) <= 0.4999999403953552
          && 0 <= a(2) && a(2) <= 5.9604641222676946E-8
          && 0 <= a(3) && a(3) <= 3.552713467042264E-15
          && 0 <= a(4) && a(4) <= 2.117582241918006E-22
          && 0 <= a(5) && a(5) <= 1.2621773731219804E-29
          && 0 <= a(6) && a(6) <= 7.5231633968471315E-37
          && 0 <= a(7) && a(7) <= 4.4841548185629436E-44
          && 0 <= a(8) && a(8) <= 2.6727645507830045E-51
          && 0 <= a(9) && a(9) <= 1.5930918161767748E-58
          && 0 <= a(10) && a(10) <= 9.495567179779856E-66
          && 0 <= a(11) && a(11) <= 5.659799086916361E-73
          && 0 <= a(12) && a(12) <= 3.373503140757299E-80
          && 0 <= a(13) && a(13) <= 2.0107645635350341E-87
          && 0 <= a(14) && a(14) <= 1.1985090753644908E-94
          && 0 <= a(15) && a(15) <= 7.143670769718235E-102
          && 0 <= a(16) && a(16) <= 4.257959586213967E-109
          && 0 <= a(17) && a(17) <= 2.5379416860425275E-116
          && 0 <= a(18) && a(18) <= 1.5127311265722081E-123
          && 0 <= a(19) && a(19) <= 9.016580144001294E-131
      } else {
        0 <= a(0) && a(0) <= 0.4999999403953552
          && 0 <= a(1) && a(1) <= 5.9604641222676946E-8
          && 0 <= a(2) && a(2) <= 3.552713467042264E-15
          && 0 <= a(3) && a(3) <= 2.117582241918006E-22
          && 0 <= a(4) && a(4) <= 1.2621773731219804E-29
          && 0 <= a(5) && a(5) <= 7.5231633968471315E-37
          && 0 <= a(6) && a(6) <= 4.4841548185629436E-44
          && 0 <= a(7) && a(7) <= 2.6727645507830045E-51
          && 0 <= a(8) && a(8) <= 1.5930918161767748E-58
          && 0 <= a(9) && a(9) <= 9.495567179779856E-66
          && 0 <= a(10) && a(10) <= 5.659799086916361E-73
          && 0 <= a(11) && a(11) <= 3.373503140757299E-80
          && 0 <= a(12) && a(12) <= 2.0107645635350341E-87
          && 0 <= a(13) && a(13) <= 1.1985090753644908E-94
          && 0 <= a(14) && a(14) <= 7.143670769718235E-102
          && 0 <= a(15) && a(15) <= 4.257959586213967E-109
          && 0 <= a(16) && a(16) <= 2.5379416860425275E-116
          && 0 <= a(17) && a(17) <= 1.5127311265722081E-123
          && 0 <= a(18) && a(18) <= 9.016580144001294E-131
          && 0 <= a(19) && a(19) <= 5.374300565720376E-138
      }
    }

    private val fwBound = Array[Double](
      6.7108864E7, // 6.7108864E7
      4.0, // 6.7108864E7 * twon24
      2.384185791015625E-7, // 6.7108864E7 * twon24 * twon24
      1.4210854715202004E-14, // 6.7108864E7 * twon24 * ... * twon24
      8.470329472543003E-22,
      5.0487097934144756E-29,
      3.009265538105056E-36,
      1.7936620343357659E-43,
      1.0691058840368783E-50,
      6.372367644529809E-58,
      3.7982270983039195E-65,
      2.263919769706678E-72,
      1.349401336733507E-79,
      8.043058733543795E-87,
      4.794036587204811E-94,
      2.8574684782056875E-101,
      1.7031839360032603E-108,
      1.0151767349262597E-115,
      6.05092486695206E-123,
      3.606632272572553E-130,
    )

    private val pow2 = Array[Double](
      5.9604645E-8,
      1.1920929E-7,
      2.3841858E-7,
      4.7683716E-7,
      9.536743E-7,
      1.9073486E-6,
      3.8146973E-6,
      7.6293945E-6,
      1.5258789E-5,
      3.0517578E-5,
      6.1035156E-5,
      1.2207031E-4,
      2.4414062E-4,
      4.8828125E-4,
      9.765625E-4,
      0.001953125,
      0.00390625,
      0.0078125,
      0.015625,
      0.03125,
      0.0625,
      0.125, // ...
      0.25, // -2
      0.5, // -1
      1.0, // 0
      2.0, // 1
      4.0, // 2
    )

    private val iqLastBound = Array[Double](
      0x7f_ffff,
      0x3f_ffff,
      0x1f_ffff,
      0x0f_ffff,
      0x07_ffff,
      0x03_ffff,
      0x01_ffff,
      0x00_ffff,
      0x00_7fff,
      0x00_3fff,
      0x00_1fff,
      0x00_0fff,
      0x00_07ff,
      0x00_03ff,
      0x00_01ff,
      0x00_00ff,
      0x00_007f,
      0x00_003f,
      0x00_001f,
      0x00_000f,
      0x00_0007,
      0x00_0003, // ...
      0x00_0001, // -2
      0x00_0000, // -1
      0x00_0000, // 0
      0x00_0000, // 1
      0x00_0000, // 2
    )

    @ignore @pure
    private def iqInv(iq: Array[Int], jz: Int, q0: Int): Boolean = {
      require(0 <= jz && jz < 20)
      require(-24 <= q0 && q0 < 3)
      iq.length == 20 && all20Int(iq, QInt)
        && iq(jz) <= iqLastBound(24 + q0)
        && (q0 != 0 || iq(jz - 1) <= 0x7f_ffff)
        && (q0 != 1 || iq(jz - 1) <= 0x3f_ffff)
        && (q0 != 2 || iq(jz - 1) <= 0x1f_ffff)
    }

    @ignore
    private def QQUB(i: Int, q0: Int): Double = {
      require(0 <= i && i < 20)
      require(-24 <= q0 && q0 < 3)
      if (i == 0)
        pow2(24 + q0) * iqLastBound(24 + q0)
      else {
        val fw = pow2(24 + q0) * twon24Pow(i)
        if (i == 1)
          if q0 == 0 then fw * 0x7f_ffff else if q0 == 1 then fw * 0x3f_ffff else if q0 == 2 then fw * 0x1f_ffff else fw * 0xff_ffff
        else
          fw * 0xff_ffff
      }
    }

    @ignore
    private def QQ(qq: Double, i: Int, jz: Int, q0: Int): Boolean = {
      require(0 <= i && i < 20)
      require(0 <= jz && jz < 20)
      require(-24 <= q0 && q0 < 3)
      if (i == 0)
        0 <= qq && qq <= pow2(24 + q0) * iqLastBound(24 + q0)
      else {
        val fw = pow2(24 + q0) * twon24Pow(i)
        if (i == 1)
          0 <= qq && (if q0 == 0 then qq <= fw * 0x7f_ffff else if q0 == 1 then qq <= fw * 0x3f_ffff else if q0 == 2 then qq <= fw * 0x1f_ffff else qq <= fw * 0xff_ffff)
        else
          0 <= qq && qq <= fw * 0xff_ffff
      }
    }

    @ignore
    private def FQ(fq: Double, i: Int, jz: Int, q0: Int): Boolean = {
      require(0 <= i && i < 20)
      require(0 <= jz && jz < 20)
      require(-24 <= q0 && q0 < 3)

      if (i == 0)
        0 <= fq && fq <= PIo2(0) * (pow2(24 + q0) * iqLastBound(24 + q0))
      else if (i == 1)
        0 <= fq && fq <= PIo2(0) * (pow2(24 + q0) * twon24Pow(1) * (if q0 == 0 then 0x7f_ffff else if q0 == 1 then 0x3f_ffff else if q0 == 2 then 0x1f_ffff else 0xff_ffff))
          + PIo2(1) * (pow2(24 + q0) * iqLastBound(24 + q0))
      else if (i == 2)
        0 <= fq && fq <= PIo2(0) * (pow2(24 + q0) * twon24Pow(2) * 0xff_ffff)
          + PIo2(1) * (pow2(24 + q0) * twon24Pow(1) * (if q0 == 0 then 0x7f_ffff else if q0 == 1 then 0x3f_ffff else if q0 == 2 then 0x1f_ffff else 0xff_ffff))
          + PIo2(2) * (pow2(24 + q0) * iqLastBound(24 + q0))
      else if (i == 3)
        0 <= fq && fq <= PIo2(0) * (pow2(24 + q0) * twon24Pow(3) * 0xff_ffff)
          + PIo2(1) * (pow2(24 + q0) * twon24Pow(2) * 0xff_ffff)
          + PIo2(2) * (pow2(24 + q0) * twon24Pow(1) * (if q0 == 0 then 0x7f_ffff else if q0 == 1 then 0x3f_ffff else if q0 == 2 then 0x1f_ffff else 0xff_ffff))
          + PIo2(3) * (pow2(24 + q0) * iqLastBound(24 + q0))
      else if (i == 4)
        0 <= fq && fq <= PIo2(0) * (pow2(24 + q0) * twon24Pow(4) * 0xff_ffff)
          + PIo2(1) * (pow2(24 + q0) * twon24Pow(3) * 0xff_ffff)
          + PIo2(2) * (pow2(24 + q0) * twon24Pow(2) * 0xff_ffff)
          + PIo2(3) * (pow2(24 + q0) * twon24Pow(1) * (if q0 == 0 then 0x7f_ffff else if q0 == 1 then 0x3f_ffff else if q0 == 2 then 0x1f_ffff else 0xff_ffff))
      else
        0 <= fq && fq <= PIo2(0) * (pow2(24 + q0) * twon24Pow(i) * 0xff_ffff)
          + PIo2(1) * (pow2(24 + q0) * twon24Pow(i - 1) * 0xff_ffff)
          + PIo2(2) * (pow2(24 + q0) * twon24Pow(i - 2) * 0xff_ffff)
          + PIo2(3) * (pow2(24 + q0) * twon24Pow(i - 3) * 0xff_ffff)
    }

    @ignore @pure
    private def qqInv2(qq: Array[Double], jz: Int, q0: Int): Boolean = {
      require(0 <= jz && jz < 20)
      require(-24 <= q0 && q0 < 3)
      qq.length == 20 && forall((x: Int) => !(0 <= x && x < 20) || QQ(qq(x), x, jz, q0))
    }

    @ignore @pure
    private def qqInvOld(qq: Array[Double], jz: Int, q0: Int): Boolean = {
      require(1 <= jz && jz <= 20)
      require(-24 <= q0 && q0 < 3)
      val fw0 = pow2(24 + q0)
      qq.length == 20
        && 0 <= qq(0) && qq(0) <= fw0 * 1 * iqLastBound(24 + q0)
        //        && 0 <= qq(1) && qq(1) <= pow2(24 + q0) * twon24Pow(1) * iqLastBound(24 + q0)
        && 0 <= qq(2) && qq(2) <= fw0 * 3.552713678800501E-15 * 0xff_ffff
        && 0 <= qq(3) && qq(3) <= fw0 * 2.1175823681357508E-22 * 0xff_ffff
        && 0 <= qq(4) && qq(4) <= fw0 * 1.2621774483536189E-29 * 0xff_ffff
        && 0 <= qq(5) && qq(5) <= fw0 * 7.52316384526264E-37 * 0xff_ffff
        && 0 <= qq(6) && qq(6) <= fw0 * 4.4841550858394146E-44 * 0xff_ffff
        && 0 <= qq(7) && qq(7) <= fw0 * 2.6727647100921956E-51 * 0xff_ffff
        && 0 <= qq(8) && qq(8) <= fw0 * 1.5930919111324523E-58 * 0xff_ffff
        && 0 <= qq(9) && qq(9) <= fw0 * 9.495567745759799E-66 * 0xff_ffff
        && 0 <= qq(10) && qq(10) <= fw0 * 5.659799424266695E-73 * 0xff_ffff
        && 0 <= qq(11) && qq(11) <= fw0 * 3.3735033418337674E-80 * 0xff_ffff
        && 0 <= qq(12) && qq(12) <= fw0 * 2.0107646833859488E-87 * 0xff_ffff
        && 0 <= qq(13) && qq(13) <= fw0 * 1.1985091468012028E-94 * 0xff_ffff
        && 0 <= qq(14) && qq(14) <= fw0 * 7.143671195514219E-102 * 0xff_ffff
        && 0 <= qq(15) && qq(15) <= fw0 * 4.2579598400081507E-109 * 0xff_ffff
        && 0 <= qq(16) && qq(16) <= fw0 * 2.5379418373156492E-116 * 0xff_ffff
        && 0 <= qq(17) && qq(17) <= fw0 * 1.512731216738015E-123 * 0xff_ffff
        && 0 <= qq(18) && qq(18) <= fw0 * 9.016580681431383E-131 * 0xff_ffff
        && 0 <= qq(19) && qq(19) <= fw0 * 5.374300886053671E-138 * 0xff_ffff
    }

    @ignore @pure
    private def fqInvOld(fq: Array[Double], jz: Int, q0: Int): Boolean = {
      require(0 <= jz && jz < 20)
      require(-24 <= q0 && q0 < 3)
      fq.length == 20 && forall((x: Int) => !(0 <= x && x < 20) || FQ(fq(x), x, jz, q0))
    }

    private val qqBoundOld = Array[Double](
      1.12589983973376E15,
      6.710886E7,
      3.999999761581421,
      2.3841856489070778E-7,
      1.4210853868169056E-14,
      8.470328967672024E-22,
      5.048709492487922E-29,
      3.0092653587388526E-36,
      1.7936619274251774E-43,
      1.0691058203132018E-50,
      6.372367264707099E-58,
      3.7982268719119425E-65,
      2.2639196347665444E-72,
      1.3494012563029196E-79,
      8.0430582541401365E-87,
      4.7940363014579633E-94,
      2.857468307887294E-101,
      1.7031838344855868E-108,
      1.015176674417011E-115,
      6.0509245062888325E-123,
    )

    private val fqBoundOld = Array[Double](
      1.76855924758968E15,
      1.9041741265023708E8,
      17.418702994662283,
      1.4077563164312565E-6,
      8.390881517119744E-14,
      5.001355121803131E-21,
      2.9810399543065615E-28,
      1.776838275376893E-35,
      1.0590781422715741E-42,
      6.312597645947779E-50,
      3.7626014029668445E-57,
      2.2426852005522516E-64,
      1.3367445472194264E-71,
      7.967618389245429E-79,
      4.749070637968438E-86,
      2.830666683893465E-93,
      1.6872088217100292E-100,
      1.0056548247993167E-107,
      5.994169859882096E-115,
      3.5728036522162535E-122,
    )

    @ignore @pure
    private def loop5Inv(fq: Array[Double]): Boolean = {
      require(fq.length == 20)
      0 <= fq(0) && fq(0) <= 1.76855924758968E15
        && 0 <= fq(1) && fq(1) <= 1.9041741265023708E8
        && 0 <= fq(2) && fq(2) <= 17.418702994662283
        && 0 <= fq(3) && fq(3) <= 1.4077563164312565E-6
        && 0 <= fq(4) && fq(4) <= 8.390881517119744E-14
        && 0 <= fq(5) && fq(5) <= 5.001355121803131E-21
        && 0 <= fq(6) && fq(6) <= 2.9810399543065615E-28
        && 0 <= fq(7) && fq(7) <= 1.776838275376893E-35
        && 0 <= fq(8) && fq(8) <= 1.0590781422715741E-42
        && 0 <= fq(9) && fq(9) <= 6.312597645947779E-50
        && 0 <= fq(10) && fq(10) <= 3.7626014029668445E-57
        && 0 <= fq(11) && fq(11) <= 2.2426852005522516E-64
        && 0 <= fq(12) && fq(12) <= 1.3367445472194264E-71
        && 0 <= fq(13) && fq(13) <= 7.967618389245429E-79
        && 0 <= fq(14) && fq(14) <= 4.749070637968438E-86
        && 0 <= fq(15) && fq(15) <= 2.830666683893465E-93
        && 0 <= fq(16) && fq(16) <= 1.6872088217100292E-100
        && 0 <= fq(17) && fq(17) <= 1.0056548247993167E-107
        && 0 <= fq(18) && fq(18) <= 5.994169859882096E-115
        && 0 <= fq(19) && fq(19) <= 3.5728036522162535E-122
    }

    @ignore @pure
    private def magic(b: Double, n: Double, i: Int): Double = {
      decreases(i)
      if i == 0 then b else n * magic(b, n, i - 1)
    }

    @ignore @opaque
    private def invertTest(iq: Array[Int], q0: Int): Double = {
      require(-24 <= q0 && q0 < 3)
      require(iq.length == 20 && all20Int(iq, QInt))
      val jz = 7
      require(q0 != 0 || 0x80_0000 <= iq(jz - 1) && iq(jz - 1) <= 0xff_ffff)
      require(q0 != 1 || 0x40_0000 <= iq(jz - 1) && iq(jz - 1) <= 0x7f_ffff)
      require(q0 != 2 || 0x20_0000 <= iq(jz - 1) && iq(jz - 1) <= 0x3f_ffff)
      var carry = 0
      var i = 0
      (while (i < jz - 1) {
        decreases(jz - i)
        val j = iq(i)
        assert(QInt(j))
        iq(i) = if carry == 0 then if j != 0 then 0x100_0000 - j else 0 else 0xff_ffff - j
        carry = if carry == 0 && j != 0 then 1 else carry
        i += 1
      }).invariant(
        0 <= i && i <= jz
          && (carry == 0 || carry == 1)
          && iq.length == 20 && all20Int(iq, QInt)
      )

      iq(jz - 1) = 0xff_ffff - iq(jz - 1) // kinda sketchy, assumes that j == jz - 1 ==> carry == 1

      assert(q0 != 0 || iq(jz - 1) <= 0x7f_ffff)
      assert(q0 != 1 || iq(jz - 1) <= 0xbf_ffff)
      assert(q0 != 2 || iq(jz - 1) <= 0xdf_ffff)

      if (q0 > 0) { // rare case: chance is 1 in 12
        if q0 == 1 then iq(jz - 1) &= 0x7f_ffff
        else if q0 == 2 then iq(jz - 1) &= 0x3f_ffff
      }

      assert(q0 != 0 || iq(jz - 1) <= 0x7f_ffff)
      assert(q0 != 1 || iq(jz - 1) <= 0x3f_ffff)
      assert(q0 != 2 || iq(jz - 1) <= 0x1f_ffff)

      //      assume(0 <= OpenJDKMath.scalb(1.0d, q0)) // TODO
      //      val z = if ih == 2 then if carry != 0 then (1.0 - z1) - OpenJDKMath.scalb(1.0, q0) else 1.0 - z1 else z1
      //      assert(0 <= z && z <= 0.5)
      0.0d
    } //.ensuring(res =>
    //      0 <= res && res <= 0.5
    //        && iq.length == 20 && all20Int(iq, QInt)
    //    )

    @ignore @opaque
    private def loop4Test(@pure iq: Array[Int], jz: Int, q0: Int): Array[Double] = {
      require(0 <= jz && jz < 20)
      require(-24 <= q0 && q0 < 3)
      //      val jz = 7
      require(iqInv(iq, jz, q0))
      //      require(iq.length == 20 && all20Int(iq, QInt))
      //      require(0 <= iq(jz) && iq(jz) <= 0x7f_ffff)
      //      require(q0 < 0 || iq(jz) == 0)
      //      require(q0 != 0 || iq(jz - 1) <= 0x7f_ffff)
      //      require(q0 != 1 || iq(jz - 1) <= 0x3f_ffff)
      //      require(q0 != 2 || iq(jz - 1) <= 0x1f_ffff)
      val q = new Array[Double](20)
      //      val fw0 = OpenJDKMath.scalb(1.0, q0)
      //      var fw = fw0
      val fw0 = pow2(24 + q0)
      //      assume(q0 != 2 || fw0 == 4.0d)
      //      assume(q0 != 1 || fw0 == 2.0d)
      //      assume(q0 != 0 || fw0 == 1.0d)
      //      assume(q0 >= 0 || 5.9604644775390625E-8 <= fw0 && fw0 <= 0.5d)
      var i = jz
      assert(-1 <= i && i <= jz)
      //      assert(0 <= fw && fw <= fw0 * twon24Pow(jz - i))
      assert(q.length == 20 && qqInv2(q, jz, q0))
      (while (i >= 0) {
        decreases(i + 1)
        assert(QInt(iq(i)))
        assert(Q(iq(i).toDouble))
        assert(q.length == 20 && qqInv2(q, jz, q0))
        val fw = fw0 * twon24Pow(jz - i)
        q(jz - i) = fw * iq(i).toDouble
        //        unfold(QQ(fw * iq(i).toDouble, jz - i, jz, q0))
        assert(QQ(fw * iq(i).toDouble, jz - i, jz, q0))
        //        q(jz - i) = pow2(24 + q0) * twon24Pow(jz - i) * iq(i).toDouble
        assert(q.length == 20 && qqInv2(q, jz, q0))
        i -= 1
        assert(-1 <= i && i <= jz)
        //        assert(fw0 <= fw && fw <= fw0 * twon24Pow(jz - i))
        assert(q.length == 20 && qqInv2(q, jz, q0))
      }).invariant(
        -1 <= i && i <= jz
          //          && 0 <= fw && fw <= fw0 * twon24Pow(jz - i)
          && q.length == 20 && qqInv2(q, jz, q0)
      )
      q
    } //.ensuring(res =>
    //        res.length == 20 && loop4Inv(res)
    //      )

    @ignore
    @opaque
    @pure
    private def loop5Test(qq: Array[Double], jz: Int, q0: Int): Array[Double] = {
      require(0 <= jz && jz < 20)
      require(-24 <= q0 && q0 < 3)
      require(qqInv2(qq, jz, q0))
      val fq = new Array[Double](20)
      val fq0 = PIo2(0) * qq(0) // 21
      assert(FQ(fq0, 0, jz, q0))
      val fq1 = PIo2(0) * qq(1) + PIo2(1) * qq(0)
      assert(FQ(fq1, 1, jz, q0))
      val fq2 = PIo2(0) * qq(2) + PIo2(1) * qq(1) + PIo2(2) * qq(0)
      assert(FQ(fq2, 2, jz, q0))
      val fq3 = PIo2(0) * qq(3) + PIo2(1) * qq(2) + PIo2(2) * qq(1) + PIo2(3) * qq(0)
      assert(FQ(fq3, 3, jz, q0))
      val fq4 = PIo2(0) * qq(4) + PIo2(1) * qq(3) + PIo2(2) * qq(2) + PIo2(3) * qq(1)
      assert(FQ(fq4, 4, jz, q0))
      val fq5 = PIo2(0) * qq(5) + PIo2(1) * qq(4) + PIo2(2) * qq(3) + PIo2(3) * qq(2)
      assert(FQ(fq5, 5, jz, q0))

      //      var i = 3
      //      (while (i <= jz) {
      //        decreases(jz + 1 - i)
      //        val fw0 = PIo2(0) * qq(i - 0)
      //        val fw1 = PIo2(1) * qq(i - 1)
      //        val fw2 = PIo2(2) * qq(i - 2)
      //        val fw3 = PIo2(3) * qq(i - 3)
      //        val fw = fw0 + fw1 + fw2 + fw3
      //        fq(i) = fw
      //        assert(qq(i - 0) + qq(i - 1) + qq(i - 2) + qq(i - 3) <= 0.5)
      //        assert(0 <= fw && fw <= PIo2(0) / 2)
      //        i += 1
      //      }).invariant(
      //        3 <= i && i <= jz + 1
      //          && fq.length == 20
      //      )
      fq
    }

    // assume that `nx == 3` and `prec == 2`
    @ignore
    private def __kernel_rem_pio2_unrolling(x: (Double, Double, Double), e0: Int): (Int, (Double, Double)) = {
      require(0 <= e0 && e0 <= 1023)
      require(0 <= x._1 && x._1 <= 0xff_ffff)
      require(0 <= x._2 && x._2 <= 0xff_ffff)
      require(0 <= x._3 && x._3 <= 0xff_ffff)

      @extern
      @pure
      def assume(P: Boolean): Unit = {}.ensuring(P)

//      val jk = 4
//      val jp = 4
      val jz = 7
//      val jx = 2
      val jv = {
        val tmp = (e0 - 3) / 24
        if tmp < 0 then 0 else tmp
      }
      val q0 = e0 - 24 * (jv + 1)
      assert(-24 <= q0 && q0 < 3)

//      // set up f[0] to f[jx+jk] where f[jx+jk] = ipio2[jv+jk]
//      j = jv - jx
//      m = jx + jz
//      i = 0
//      while (i <= m) { // max iterations: 7
//        f(i) = if (j < 0) 0.0
//        else two_over_pi(j).toDouble
//        i += 1
//        j += 1
//      }

      // - loop is wrapped in opaque local function to prevent inox from unrolling the loop
      // - we cannot copy-paste-unroll the loop since stainless/inox will create multiple copies of `two_over_pi` in the smt query in this case
      // - using `two_over_pi` in the postcondition is also problematic since multiple copies are created
      @opaque
      def loop1(): Array[Double] = {
        val f = new Array[Double](20)
        var i = 0
        (while (i <= 2 + jz) {
          decreases(2 + jz + 1 - i)
          if jv - 2 + i >= 0 then f(i) = two_over_pi(jv - 2 + i).toDouble
          i += 1
        }).invariant(
          0 <= i && i <= 2 + jz + 1
            && f.length == 20 && all20(f, Q)
        )
        f
      }.ensuring(res =>
        res.length == 20 && all20(res, Q)
      )

      val f = loop1()
      // `f` now contains 24-bit chunks of two over pi
      assert(all20(f, Q))

//      // compute q[0],q[1],...q[jk]
//      i = 0
//      while (i <= jz) {
//        fw = 0.0
//        if (0 <= jx) {
//          fw += x._1 * f(jx + i)
//          if (1 <= jx) {
//            fw += x._2 * f(jx + i - 1)
//            if (2 <= jx) {
//              fw += x._3 * f(jx + i - 2)
//            }
//          }
//        }
//        q(i) = fw
//        i += 1
//      }

      @opaque
      def loop2(): Array[Double] = {
        val q = new Array[Double](20)
        var i = 0
        (while (i <= jz) {
          decreases(jz + 1 - i)
          q(i) = x._1 * f(i + 2) + x._2 * f(i + 1) + x._3 * f(i)
          assert(Q(f(i + 2)))
          assert(Q(f(i + 1)))
          assert(Q(f(i)))
          assert(P(q(i)))
          i += 1
        }).invariant(
          0 <= i && i <= jz + 1
            && q.length == 20 && all20(q, P)
        )
        q
      }.ensuring(res =>
        res.length == 20 && all20(res, P)
      )

      val q = loop2()
      // q now contains chunks of `2 / pi * x`
      assert(q.length == 20 && all20(q, P))

//      // distill q[] into iq[] reversingly
//      i = 0
//      j = jz
//      z = q(jz)
//      while (j > 0) { // max iterations: 4
//        fw = (twon24 * z).toInt.toDouble
//        iq(i) = (z - TWO24 * fw).toInt
//        z = q(j - 1) + fw
//        i += 1
//        j -= 1
//      }

      @opaque
      def loop3(iq: Array[Int], @pure q: Array[Double]): Double = {
        require(iq.length == 20 && all20Int(iq, QInt))
        require(q.length == 20 && all20(q, P))
        var j = jz
        var z = q(jz)

//        assert(0 <= z && z <= 3 * 0xffff_ffff_ffffL)
//        assert(0 <= (twon24 * z).toInt.toDouble && (twon24 * z).toInt.toDouble <= 0x2ff_ffff)
//        assert(TWO24 * (twon24 * z).toInt.toDouble <= 0x2_ffff_ff00_0000L)
//        assert((z - TWO24 * (twon24 * z).toInt.toDouble).toInt <= 0xff_ffff)
//        assert(QInt((z - TWO24 * (twon24 * z).toInt.toDouble).toInt))

//        var fw = (twon24 * z).toInt.toDouble
//        iq(jz - j) = (z - TWO24 * fw).toInt
//        assert(QInt(iq(jz - j)))
//        assert(0 <= fw && fw <= 0x2ff_ffff)
//        assert(P(q(j - 1)))
//        z = q(j - 1) + fw
//        j -= 1
//        assert(0 <= z && z <= 3 * 0xffff_ffff_ffffL + 0x2ff_ffff)
//
//        fw = (twon24 * z).toInt.toDouble
//        iq(jz - j) = (z - TWO24 * fw).toInt
//        assert(QInt(iq(jz - j)))
//        assert(0 <= fw && fw <= 0x300_0002)
//        assert(P(q(j - 1)))
//        z = q(j - 1) + fw
//        j -= 1
//        assert(0 <= z && z <= 3 * 0xffff_ffff_ffffL + 0x300_0002)

        (while (j > 0) {
          decreases(j)
          val fw = (twon24 * z).toInt.toDouble
          iq(jz - j) = (z - TWO24 * fw).toInt
          assert(QInt(iq(jz - j)))
          assert(0 <= fw && fw <= 0x300_0002)
          assert(P(q(j - 1)))
          z = q(j - 1) + fw
          j -= 1
        }).invariant(
          0 <= j && j <= jz
            && 0 <= z && z <= 3 * 0xffff_ffff_ffffL + 0x300_0002
            && iq.length == 20 && all20Int(iq, QInt)
        )
        z
      }.ensuring(res =>
        iq.length == 20 && all20Int(iq, QInt)
          && 0 <= res && res <= 3 * 0xffff_ffff_ffffL + 0x300_0002
      )

      val iq = new Array[Int](20)
      val z0 = loop3(iq, q)

      // `iq` now contains 24 bit chunks of `q = 2 / pi * x` in reversed order; the highest bits of `q` are in `z0`
      assert(iq.length == 20 && all20Int(iq, QInt))
      assert(0 <= z0 && z0 <= 3 * 0xffff_ffff_ffffL + 0x300_0002)

      // remove integer part and compute n
//      z = OpenJDKMath.scalb(z, q0) // actual value of z
//      z -= 8.0 * OpenJDKMath.floor(z * 0.125) // trim off integer >= 8
//      val n0 = z.toInt
//      z -= n0.toDouble
//      val n1 = n0 + (if q0 > 0 then iq(jz - 1) >> (24 - q0) else 0)
//      val ih = if (q0 >= 0) {
//        i = iq(jz - 1) >> (24 - q0)
//        iq(jz - 1) -= i << (24 - q0)
//        iq(jz - 1) >> (23 - q0)
//      }
//      else if (z >= 0.5) 2
//      else 0
//      val n = n1 + (if ih > 0 then 1 else 0)

      @opaque
      def removeInteger(iq: Array[Int]): (Double, Int, Int) = {
        require(iq.length == 20 && all20Int(iq, QInt))
        var z = OpenJDKMath.scalb(z0, q0)
        z -= 8.0 * OpenJDKMath.floor(z * 0.125)
        assume(0 <= z && z < 8) // TODO
        val n0 = z.toInt
        z -= n0.toDouble
        assert(0 <= z && z < 1)
        assume(q0 < 0 || z == 0) // TODO
        assume(q0 >= 0 || OpenJDKMath.scalb(1.0d, q0) <= 1.0d - z) // TODO
        assert(QInt(iq(jz - 1)))
        val n1 = n0 + (if q0 > 0 then iq(jz - 1) >> (24 - q0) else 0)
        assert(0 <= n1 && n1 <= 10)
        val (ih, j) = if (q0 >= 0) {
          assert(QInt(iq(jz - 1)))
          val i = (iq(jz - 1) >> (24 - q0)) << (24 - q0)
          assert(i == 0 || i == 1 << 23 || i == 1 << 22 || i == 3 << 22)
          val j = iq(jz - 1) - i
          (j >> (23 - q0), j)
        }
        else if (z >= 0.5) (2, iq(jz - 1))
        else (0, iq(jz - 1))
        assert(QInt(j))
        iq(jz - 1) = j
        assert(q0 != 0 || iq(jz - 1) <= 0xff_ffff)
        assert(q0 != 1 || iq(jz - 1) <= 0x7f_ffff)
        assert(q0 != 2 || iq(jz - 1) <= 0x3f_ffff)
        assert(q0 != 0 || ih == 0 || 0x80_0000 <= iq(jz - 1))
        assert(q0 != 1 || ih == 0 || 0x40_0000 <= iq(jz - 1))
        assert(q0 != 2 || ih == 0 || 0x20_0000 <= iq(jz - 1))
        assert(iq.length == 20 && all20Int(iq, QInt))
        assert(0 <= ih && ih <= 2)
        assert((ih == 2) == (z >= 0.5 && q0 < 0))
        val n = n1 + (if ih > 0 then 1 else 0)
        assert(0 <= n && n <= 11)
        (z, n, ih)
      }.ensuring(res =>
        iq.length == 20 && all20Int(iq, QInt)
          && 0 <= res._1 && res._1 < 1.0d
          && (q0 < 0 || res._1 == 0)
          && (q0 >= 0 || OpenJDKMath.scalb(1.0d, q0) <= 1.0d - res._1)
          && 0 <= res._2 && res._2 <= 11
          && 0 <= res._3 && res._3 <= 2
          && ((res._3 == 2) == (res._1 >= 0.5 && q0 < 0))
          && (q0 != 0 || res._3 == 0 || (0x80_0000 <= iq(jz - 1) && iq(jz - 1) <= 0xff_ffff))
          && (q0 != 1 || res._3 == 0 || (0x40_0000 <= iq(jz - 1) && iq(jz - 1) <= 0x7f_ffff))
          && (q0 != 2 || res._3 == 0 || (0x20_0000 <= iq(jz - 1) && iq(jz - 1) <= 0x3f_ffff))
      )

      val (z1, n, ih) = removeInteger(iq)

      // TODO: update and double-check comments here
      // `iq` now contains 24 bit chunks of `q = 2 / pi * x` modulo 1; the highest bits of `q` are in `z0`
      assert(iq.length == 20 && all20Int(iq, QInt))
      // `z1` is the actual, correctly scaled, value represented by the highest bits of `q = 2 / pi * x` modulo 1
      assert(0 <= z1 && z1 < 1.0d)
      assert(q0 >= 0 || OpenJDKMath.scalb(1.0d, q0) <= 1.0d - z1)
      assert(q0 < 0 || z1 == 0)
      // `n modulo 8` indicates which chunk of the interval `[0, 1]` that `q modulo 1` falls in, where `q` is correctly scaled
      assert(0 <= n && n <= 11)
      // `ih > 0` iff `q >= 0.5`, where `q` is correctly scaled; `ih == 2` iff `z1 >= 0.5 && q0 < 0`
      assert(0 <= ih && ih <= 2)
      assert((ih == 2) == (z1 >= 0.5 && q0 < 0))

      // compute `1 - q` if `q >= 0.5`
//      if (ih > 0) { // q > 0.5
//        carry = 0
//        i = 0
//        while (i < jz) { // compute 1-q
//          val j = iq(i)
//          iq(i) = if carry == 0 then if j != 0 then 0x100_0000 - j else 0 else 0xff_ffff - j
//          carry = if carry == 0 && j != 0 then 1 else carry
//          i += 1
//        }
//        if (q0 > 0) { // rare case: chance is 1 in 12
//          q0 match {
//            case 1 =>
//              iq(jz - 1) &= 0x7f_ffff
//            case 2 =>
//              iq(jz - 1) &= 0x3f_ffff
//          }
//        }
//        if (ih == 2) {
//          z = 1.0 - z
//          if (carry != 0)
//            z -= OpenJDKMath.scalb(1.0, q0)
//        }
//      }

      @opaque
      def invert(iq: Array[Int]): Double = {
        require(-24 <= q0 && q0 < 3)
        require(iq.length == 20 && all20Int(iq, QInt))
        require(q0 != 0 || 0x80_0000 <= iq(jz - 1) && iq(jz - 1) <= 0xff_ffff)
        require(q0 != 1 || 0x40_0000 <= iq(jz - 1) && iq(jz - 1) <= 0x7f_ffff)
        require(q0 != 2 || 0x20_0000 <= iq(jz - 1) && iq(jz - 1) <= 0x3f_ffff)
        var carry = 0
        var i = 0
        (while (i < jz - 1) {
          decreases(jz - i)
          val j = iq(i)
          assert(QInt(j))
          iq(i) = if carry == 0 then if j != 0 then 0x100_0000 - j else 0 else 0xff_ffff - j
          carry = if carry == 0 && j != 0 then 1 else carry
          i += 1
        }).invariant(
          0 <= i && i <= jz
            && (carry == 0 || carry == 1)
            && iq.length == 20 && all20Int(iq, QInt)
        )

        iq(jz - 1) = 0xff_ffff - iq(jz - 1) // kinda sketchy, assumes that j == jz - 1 ==> carry == 1

        assert(q0 != 0 || iq(jz - 1) <= 0x7f_ffff)
        assert(q0 != 1 || iq(jz - 1) <= 0xbf_ffff)
        assert(q0 != 2 || iq(jz - 1) <= 0xdf_ffff)

        if (q0 > 0) { // rare case: chance is 1 in 12
          if q0 == 1 then iq(jz - 1) &= 0x7f_ffff
          else if q0 == 2 then iq(jz - 1) &= 0x3f_ffff
        }

        assert(q0 != 0 || iq(jz - 1) <= 0x7f_ffff)
        assert(q0 != 1 || iq(jz - 1) <= 0x3f_ffff)
        assert(q0 != 2 || iq(jz - 1) <= 0x1f_ffff)

        assume(5.9604644775390625E-8 <= OpenJDKMath.scalb(1.0d, q0)) // TODO
        assume(ih == 2)
        val z = if ih == 2 then (1.0 - z1) - OpenJDKMath.scalb(1.0, q0) else z1 // assumes that j == jz ==> carry == 1
        assert(0 <= z && z < 0.5)
        z
      }.ensuring(res =>
        0 <= res && res < 0.5
          && iq.length == 20 && all20Int(iq, QInt)
          && (q0 != 0 || iq(jz - 1) <= 0x7f_ffff)
          && (q0 != 1 || iq(jz - 1) <= 0x3f_ffff)
          && (q0 != 2 || iq(jz - 1) <= 0x1f_ffff)
      )

      val z2 = if ih > 0 then invert(iq) else z1

      assert(0 <= z2 && z2 < 0.5)
      assert(iq.length == 20 && all20Int(iq, QInt))
      assert(q0 != 0 || iq(jz - 1) <= 0x7f_ffff) // ???????????????
      assert(q0 != 1 || iq(jz - 1) <= 0x3f_ffff)
      assert(q0 != 2 || iq(jz - 1) <= 0x1f_ffff)

//      z = OpenJDKMath.scalb(z, -q0)
//      fw = (twon24 * z).toInt.toDouble
//      iq(jz) = (z - TWO24 * fw).toInt
//      val jz_1 = jz + 1
//      val q0_1 = q0 + 24
//      iq(jz_1) = fw.toInt

//      @opaque
//      def split(iq: Array[Int]): Unit = {
//        require(iq.length == 20 && all20Int(iq, QInt))
//        val z = OpenJDKMath.scalb(z2, -q0)
//        assume(0 <= z && z <= 0xff_ffffL) // TODO
//        val fw = (twon24 * z).toInt.toDouble
//        assert(fw == 0)
//        iq(jz) = (z - TWO24 * fw).toInt
//        assert(Q(fw))
//        assert(QInt(iq(jz)))
//        iq(jz + 1) = fw.toInt
//        assert(QInt(jz + 1))
//      }.ensuring(
//        iq.length == 20 && all20Int(iq, QInt)
//      )
//
//      split(iq)
//      val jz_1 = jz + 1
//      val q0_1 = q0 + 24

      iq(jz) = OpenJDKMath.scalb(z2, -q0).toInt
      assume(0 <= iq(jz) && iq(jz) <= 0x7f_ffff) // TODO
      assume(q0 < 0 || iq(jz) == 0) // TODO
      assert(iq.length == 20 && all20Int(iq, QInt))
      assert(q0 != 0 || iq(jz - 1) <= 0x7f_ffff)
      assert(q0 != 1 || iq(jz - 1) <= 0x3f_ffff)
      assert(q0 != 2 || iq(jz - 1) <= 0x1f_ffff)

      // convert integer "bit" chunk to floating-point value
//      fw = OpenJDKMath.scalb(1.0, q0_1)
//      i = jz_1
//      while (i >= 0) {
//        q(i) = fw * iq(i).toDouble
//        fw *= twon24
//        i -= 1
//      }

      @opaque
      def loop4(@pure iq: Array[Int]): Array[Double] = {
        require(iq.length == 20 && all20Int(iq, QInt))
        require(0 <= iq(jz) && iq(jz) <= 0x7f_ffff)
        require(q0 < 0 || iq(jz) == 0)
        require(q0 != 0 || iq(jz - 1) <= 0x7f_ffff)
        require(q0 != 1 || iq(jz - 1) <= 0x3f_ffff)
        require(q0 != 2 || iq(jz - 1) <= 0x1f_ffff)
        val q = new Array[Double](20)
        val fw0 = OpenJDKMath.scalb(1.0, q0)
        var fw = fw0
        assume(q0 != 2 || fw0 == 4.0d)
        assume(q0 != 1 || fw0 == 2.0d)
        assume(q0 != 0 || fw0 == 1.0d)
        assume(q0 >= 0 || fw0 <= 0.5d)
        var i = jz
        (while (i >= 0) {
          decreases(i + 1)
          assert(QInt(iq(i)))
          assert(Q(iq(i).toDouble))
          q(jz - i) = fw * iq(i).toDouble
          fw = fw * twon24
          i -= 1
        }).invariant(
          -1 <= i && i <= jz
            && 0 <= fw && fw <= fw0 * twon24Pow(jz - i)
            && q.length == 20 && loop4InvNew2(q, q0)
        )
        q
      }.ensuring(res =>
        res.length == 20 && loop4Inv(res)
      )

      // order of `qq` is revered compared with openJDK to improve SMT solver performance
      val qq = loop4(iq)
      assert(qq.length == 20 && loop4Inv(qq))

      // compute PIo2[0,...,jp]*q[jz,...,0]
//      i = jz_1
//      while (i >= 0) {
//        fw = 0.0
//        k = 0
//        while (k <= jp && k <= jz_1 - i) {
//          fw += PIo2(k) * q(i + k)
//          k += 1
//        }
//        fq(jz_1 - i) = fw
//        i -= 1
//      }

      @opaque
      def loop5(): Array[Double] = {
        val fq = new Array[Double](20)
        var i = 3
        assert(loop4Inv(qq))
        (while (i <= jz) {
          decreases(jz + 1 - i)
          val fw0 = PIo2(0) * qq(i - 0)
          val fw1 = PIo2(1) * qq(i - 1)
          val fw2 = PIo2(2) * qq(i - 2)
          val fw3 = PIo2(3) * qq(i - 3)
          val fw = fw0 + fw1 + fw2 + fw3
          assert(0 <= fw0 && fw0 <= PIo2(0) * qqBoundOld(i - 0))
          assert(0 <= fw1 && fw1 <= PIo2(1) * qqBoundOld(i - 1))
          assert(0 <= fw2 && fw2 <= PIo2(2) * qqBoundOld(i - 2))
          assert(0 <= fw3 && fw3 <= PIo2(3) * qqBoundOld(i - 3))
          fq(i) = fw
          assert(0 <= fq(i) && fq(i) <= fqBoundOld(i))
          i += 1
        }).invariant(
          3 <= i && i <= jz + 1
            && fq.length == 20 && loop5Inv(fq)
        )
        fq
      }.ensuring(res =>
        res.length == 20 && loop5Inv(res)
      )

      val fq = loop5()

      (0, (0, 0))
    }

    @ignore
    private def __kernel_rem_pio2_prec_2_simplified_functional(x: (Double, Double, Double), e0: Int): (Int, (Double, Double)) = {
      require(-1024 <= e0 && e0 <= 1024)
      val iq = new Array[Int](20)
      val f = new Array[Double](20)
      val fq = new Array[Double](20)
      val q = new Array[Double](20)
      val jk = 4
      val jp = 4
      val jz = 7
      val jx = 2
      val jv = {
        val tmp = (e0 - 3) / 24
        if tmp < 0 then 0 else tmp
      }
      val q0 = e0 - 24 * (jv + 1)
      assert(q0 < 3)

      def tmp1(): Unit = {
        f(0) = if jv - jx + 0 < 0 then 0.0d else two_over_pi(0).toDouble
        f(1) = if jv - jx + 1 < 0 then 0.0d else two_over_pi(1).toDouble
        f(2) = if jv - jx + 2 < 0 then 0.0d else two_over_pi(2).toDouble
        f(3) = if jv - jx + 3 < 0 then 0.0d else two_over_pi(3).toDouble
        f(4) = if jv - jx + 4 < 0 then 0.0d else two_over_pi(4).toDouble
        f(5) = if jv - jx + 5 < 0 then 0.0d else two_over_pi(5).toDouble
        f(6) = if jv - jx + 6 < 0 then 0.0d else two_over_pi(6).toDouble
        f(7) = if jv - jx + 7 < 0 then 0.0d else two_over_pi(7).toDouble
        f(8) = if jv - jx + 8 < 0 then 0.0d else two_over_pi(8).toDouble
        f(9) = if jv - jx + 9 < 0 then 0.0d else two_over_pi(9).toDouble
      }

      tmp1()

      assert(forall((x: Int) => !(0 <= x && x < 20 && jx - jv < x && x < jx + jz) || f(x) == two_over_pi(x).toDouble))
      assert(forall((x: Int) => !(0 <= x && x < 20) || f(x).isZero || f(x) == two_over_pi(x).toDouble))

      def tmp2(): Unit = {
        q(0) = x._1 * f(jx + 0) + x._2 * f(jx + 0 - 1) + x._3 * f(jx + 0 - 2)
        q(1) = x._1 * f(jx + 1) + x._2 * f(jx + 1 - 1) + x._3 * f(jx + 1 - 2)
        q(2) = x._1 * f(jx + 2) + x._2 * f(jx + 2 - 1) + x._3 * f(jx + 2 - 2)
        q(3) = x._1 * f(jx + 3) + x._2 * f(jx + 3 - 1) + x._3 * f(jx + 3 - 2)
        q(4) = x._1 * f(jx + 4) + x._2 * f(jx + 4 - 1) + x._3 * f(jx + 4 - 2)
        q(5) = x._1 * f(jx + 5) + x._2 * f(jx + 5 - 1) + x._3 * f(jx + 5 - 2)
        q(6) = x._1 * f(jx + 6) + x._2 * f(jx + 6 - 1) + x._3 * f(jx + 6 - 2)
        q(7) = x._1 * f(jx + 7) + x._2 * f(jx + 7 - 1) + x._3 * f(jx + 7 - 2)
      }

      tmp2()

      // distill q[] into iq[] reversingly
      def tmp3(): Double = {
        val z0 = q(jz)
        val fw0 = (twon24 * z0).toInt.toDouble
        iq(0) = (z0 - TWO24 * fw0).toInt
        val z1 = q(jz - 0 - 1) + fw0
        val fw1 = (twon24 * z1).toInt.toDouble
        iq(1) = (z1 - TWO24 * fw1).toInt
        val z2 = q(jz - 1 - 1) + fw1
        val fw2 = (twon24 * z2).toInt.toDouble
        iq(2) = (z2 - TWO24 * fw2).toInt
        val z3 = q(jz - 2 - 1) + fw2
        val fw3 = (twon24 * z3).toInt.toDouble
        iq(3) = (z3 - TWO24 * fw3).toInt
        val z4 = q(jz - 3 - 1) + fw3
        val fw4 = (twon24 * z4).toInt.toDouble
        iq(4) = (z4 - TWO24 * fw4).toInt
        val z5 = q(jz - 4 - 1) + fw4
        val fw5 = (twon24 * z5).toInt.toDouble
        iq(5) = (z5 - TWO24 * fw5).toInt
        val z6 = q(jz - 5 - 1) + fw5
        val fw6 = (twon24 * z6).toInt.toDouble
        iq(6) = (z6 - TWO24 * fw6).toInt
        q(jz - 6 - 1) + fw6
      }

      val z7 = tmp3()

      // compute n
      val zz0 = OpenJDKMath.scalb(z7, q0) // actual value of z
      val zz1 = zz0 - 8.0 * OpenJDKMath.floor(zz0 * 0.125) // trim off integer >= 8
      val n0 = zz1.toInt
      val zz2 = zz1 - n0.toDouble
      val n1 = n0 + (if q0 > 0 then iq(jz - 1) >> (24 - q0) else 0)
      val ih = if (q0 >= 0) {
        val i = iq(jz - 1) >> (24 - q0)
        iq(jz - 1) -= i << (24 - q0)
        iq(jz - 1) >> (23 - q0)
      }
      else if (zz2 >= 0.5) 2
      else 0

      // compute 1 - q if necessary
      if (ih > 0) { // q > 0.5
        def tmp4(): Unit = {
          val j0 = iq(0)
          val carry0 = if j0 != 0 then 1 else 0
          iq(0) = if j0 != 0 then 0x100_0000 - j0 else 0
          val j1 = iq(1)
          iq(1) = if carry0 == 0 then if j1 != 0 then 0x100_0000 - j1 else 0 else 0xff_ffff - j1
          val carry1 = if carry0 == 0 && j1 != 0 then 1 else carry0
          val j2 = iq(2)
          iq(2) = if carry1 == 0 then if j2 != 0 then 0x100_0000 - j2 else 0 else 0xff_ffff - j2
          val carry2 = if carry1 == 0 && j2 != 0 then 1 else carry1
          val j3 = iq(3)
          iq(3) = if carry2 == 0 then if j3 != 0 then 0x100_0000 - j3 else 0 else 0xff_ffff - j3
          val carry3 = if carry2 == 0 && j3 != 0 then 1 else carry2
          val j4 = iq(4)
          iq(4) = if carry3 == 0 then if j4 != 0 then 0x100_0000 - j3 else 0 else 0xff_ffff - j3
          val carry4 = if carry3 == 0 && j4 != 0 then 1 else carry3
          val j5 = iq(5)
          iq(5) = if carry4 == 0 then if j5 != 0 then 0x100_0000 - j5 else 0 else 0xff_ffff - j5
          val carry5 = if carry4 == 0 && j5 != 0 then 1 else carry4
          val j6 = iq(6)
          iq(6) = if carry5 == 0 then if j6 != 0 then 0x100_0000 - j6 else 0 else 0xff_ffff - j6
          val carry6 = if carry5 == 0 && j6 != 0 then 1 else carry5
        }

        tmp4()

        // rare case: chance is 1 in 12
        if (q0 == 1) iq(jz - 1) &= 0x7f_ffff
        if (q0 == 2) iq(jz - 1) &= 0x3f_ffff
      }

      (0, (0, 0))
    }

    @ignore
    private def loop1Post(jx: Int, jz: Int, jv: Int, f: Array[Double]): Boolean = {
      f.length == 20 && forall((x: Int) => !(0 <= x && x <= jx + jz) || f(x) == (if jv - jx + x < 0 then 0.0d else two_over_pi(x).toDouble))
    }

    @ignore
    private def bounded_forall_double(lo: Int, hi: Int, a: Array[Double], P: Double => Boolean): Boolean = {
      decreases(hi - lo + 1)
      if hi < lo then true else P(a(hi - 1)) && bounded_forall_double(lo, hi - 1, a, P)
    }.ensuring(_ => a == old(a) && a.length == old(a).length)

    @ignore @opaque
    private def loop1___(jx: Int, jz: Int, jv: Int): Array[Double] = {
      require(0 <= jx && jx <= 2)
      require(0 <= jz && jz <= 17)
      require(0 <= jv && jv <= 100)
      val f = new Array[Double](20)
      var i = 0
      (while (i <= jx + jz) {
        decreases(jx + jz - i)
        f(i) = if jv - jx + i < 0 then 0.0d else two_over_pi(i).toDouble
        i += 1
      }).invariant(
        0 <= i && i <= jx + jz + 1
          && f.length == 20
          && forall((x: Int) => !(0 <= x && x < i) || f(x) == (if jv - jx + x < 0 then 0.0d else two_over_pi(x).toDouble))
      )
      f
    }.ensuring(res => loop1Post(jx, jz, jv, res))

    @ignore
    private def __kernel_rem_pio2_prec_2_simplified(x: (Double, Double, Double), e0: Int): (Int, (Double, Double)) = {
      import stainless.lang.StaticChecks.*
      require(-1023 <= e0 && e0 <= 1023)
      require(0 <= x._1 && x._1 <= 0xff_ffff)
      require(0 <= x._2 && x._2 <= 0xff_ffff)
      require(0 <= x._3 && x._3 <= 0xff_ffff)
      val jz = 7
      val jx = 2
      val jv = {
        val tmp = (e0 - 3) / 24
        if tmp < 0 then 0 else tmp
      }
      val q0 = e0 - 24 * (jv + 1)
      assert(q0 < 3)

      @opaque
      def loop1(): Array[Double] = {
        val f = new Array[Double](20)
        var i = 0
        (while (i <= jx + jz) {
          decreases(jx + jz - i)
          f(i) = if jv - jx + i < 0 then 0.0d else two_over_pi(jv - jx + i).toDouble
          i += 1
        }).invariant(
          0 <= i && i <= jx + jz + 1
            && f.length == 20
            && forall((x: Int) => !(0 <= x && x < 20 && x < jx - jv) || f(x).isZero)
            && forall((x: Int) => !(0 <= x && x < i && jx - jv <= x && x <= jx + jz) || f(x) == two_over_pi(jv - jx + x).toDouble)
            && forall((x: Int) => !(0 <= x && x < 20 && jx + jz < x) || f(x).isZero)
        )
        f
      }.ensuring(res =>
        res.length == 20
//          && forall((x: Int) => !(0 <= x && x < 20 && x < jx - jv) || res(x).isZero)
//          && forall((x: Int) => !(0 <= x && x < 20 && jx - jv <= x && x <= jx + jz) || res(x) == two_over_pi(jv - jx + x).toDouble)
//          && forall((x: Int) => !(0 <= x && x < 20 && jx + jz < x) || res(x).isZero)
          && forall((x: Int) => !(0 <= x && x < 20) || 0 <= res(x) && res(x) <= 0xff_ffff)
      )

      val f = loop1()

//      @opaque
//      def loop2(): Array[Double] = {
//        val q = new Array[Double](20)
//        assert(q.length == 20)
//        var j = 0
//        (while (j <= jz) {
//          decreases(jz + 1 - j)
//          q(j) = x._1 * f(jx + j) + x._2 * f(jx + j - 1) + x._3 * f(jx + j - 2)
//          assert(0 <= q(j) && q(j) <= 3 * 0xffff_ffff_ffffL)
//          assert(q.length == 20)
//          j += 1
//        }).invariant(
//          0 <= j && j <= jz + 1
//            && q.length == 20 && f.length == 20
//            && forall((x: Int) => !(0 <= x && x < j) || 0 <= q(x) && q(x) <= 3 * 0xffff_ffff_ffffL)
////            && bounded_forall_double(0, j, q, P)
////            && 0 <= q(0) && q(0) <= 3 * 0xffff_ffff_ffffL
////            && 0 <= q(1) && q(1) <= 3 * 0xffff_ffff_ffffL
////            && 0 <= q(2) && q(2) <= 3 * 0xffff_ffff_ffffL
////            && 0 <= q(3) && q(3) <= 3 * 0xffff_ffff_ffffL
////            && 0 <= q(4) && q(4) <= 3 * 0xffff_ffff_ffffL
////            && 0 <= q(5) && q(5) <= 3 * 0xffff_ffff_ffffL
////            && 0 <= q(6) && q(6) <= 3 * 0xffff_ffff_ffffL
////            && 0 <= q(7) && q(7) <= 3 * 0xffff_ffff_ffffL
//        )
//        assert(forall((x: Int) => !(0 <= x && x < j) || 0 <= q(x) && q(x) <= 3 * 0xffff_ffff_ffffL))
////        assert(bounded_forall_double(0, j, q, P))
//        q
//      }.ensuring(res =>
//        res.length == 20
//          && forall((x: Int) => !(0 <= x && x <= jz) || 0 <= res(x) && res(x) <= 3 * 0xffff_ffff_ffffL)
//      )

      @opaque
      def loop2(): Array[Double] = {
        def whileLoop(j: Int, q: Array[Double]): (Int, Array[Double]) = {
          require(0 <= j && j <= jz)
          require(q.length == 20 && f.length == 20)
          require(forall((x: Int) => !(0 <= x && x < j) || 0 <= q(x) && q(x) <= 3 * 0xffff_ffff_ffffL))
          decreases(jz - j)
          val q1 = q.updated(j, x._1 * f(jx + j) + x._2 * f(jx + j - 1) + x._3 * f(jx + j - 2))
          val j1 = j + 1
          assert(forall((x: Int) => !(0 <= x && x < j) || q(x) == q1(x)))
          assert(forall((x: Int) => !(0 <= x && x < j) || 0 <= q1(x) && q1(x) <= 3 * 0xffff_ffff_ffffL))
          assert(0 <= q1(j) && q1(j) <= 3 * 0xffff_ffff_ffffL)
          assert(forall((x: Int) => !(0 <= x && x < j1) || 0 <= q1(x) && q1(x) <= 3 * 0xffff_ffff_ffffL))
          if j1 > jz then (j1, q1) else whileLoop(j1, q1)
        }.ensuring(res =>
          res._1 == jz + 1 && res._2.length == 20 && f.length == 20
            && forall((x: Int) => !(0 <= x && x < res._1) || 0 <= res._2(x) && res._2(x) <= 3 * 0xffff_ffff_ffffL)
            && forall((x: Int) => !(0 <= x && x < j) || res._2(x) == q(x))
        )
        val res = whileLoop(0, new Array[Double](20))
        assert(forall((x: Int) => !(0 <= x && x < res._1) || 0 <= res._2(x) && res._2(x) <= 3 * 0xffff_ffff_ffffL))
        res._2
      }.ensuring(res =>
        res.length == 20
          && forall((x: Int) => !(0 <= x && x <= jz) || 0 <= res(x) && res(x) <= 3 * 0xffff_ffff_ffffL)
      )

      val q = loop2()

      @opaque
      def loop3(): (Array[Int], Double) = {
        val iq = new Array[Int](20)
        var z = q(jz)
        var j = jz
        (while (j > 0) {
          decreases(j)
          val fw = (twon24 * z).toInt.toDouble
          iq(jz - j) = (z - TWO24 * fw).toInt
          z = q(j - 1) + fw
          j -= 1
        }).invariant(
          0 <= j && j <= jz
            && q.length == 20 && iq.length == 20
            && forall((x: Int) => !(0 <= x && x < j) || 0 <= iq(x) && iq(x) <= 0xff_ffff)
        )
        (iq, z)
      }.ensuring(res =>
          res._1.length == 20
          && forall((x: Int) => !(0 <= x && x < 20) || 0 <= res._1(x) && res._1(x) <= 0xff_ffff)
      )

      val tmp = loop3()
      val iq = tmp._1

      // compute n
      var z = tmp._2
      z = OpenJDKMath.scalb(z, q0) // actual value of z
      z -= 8.0 * OpenJDKMath.floor(z * 0.125) // trim off integer >= 8
      val n0 = z.toInt
      z -= n0.toDouble
      val n1 = n0 + (if q0 > 0 then iq(jz - 1) >> (24 - q0) else 0)
      val ih = if (q0 >= 0) {
        val i = iq(jz - 1) >> (24 - q0)
        iq(jz - 1) -= i << (24 - q0)
        iq(jz - 1) >> (23 - q0)
      }
      else if (z >= 0.5) 2
      else 0
      val n = n1 + (if ih > 0 then 1 else 0)

      if (ih > 0) { // q > 0.5, compute 1-q
        @opaque
        def loop4(): Int = {
          var carry = 0
          var i = 0
          (while (i < jz) {
            decreases(jz - i)
            val j = iq(i)
            iq(i) = if carry == 0 then if j != 0 then 0x100_0000 - j else 0 else 0xff_ffff - j
            carry = if carry == 0 && j != 0 then 1 else carry
            i += 1
          }).invariant(
            0 <= i && i <= jz
              && iq.length == 20
          )
          carry
        }.ensuring(_ =>
          iq.length == 20
        )
        val carry = loop4()
        if (q0 == 1) iq(jz - 1) &= 0x7f_ffff
        if (q0 == 2) iq(jz - 1) &= 0x3f_ffff
        if (ih == 2) {
          z = 1.0 - z
          if (carry != 0)
            z -= OpenJDKMath.scalb(1.0, q0)
        }
      }

      z = OpenJDKMath.scalb(z, -q0)
      val fw = (twon24 * z).toInt.toDouble
      iq(jz) = (z - TWO24 * fw).toInt
      val jz_1 = jz + 1
      val q0_1 = q0 + 24
      iq(jz_1) = fw.toInt

      // convert integer "bit" chunk to floating-point value
      @opaque
      def loop5(): Unit = {
        var fw = OpenJDKMath.scalb(1.0, q0_1)
        var i = jz_1
        (while (i >= 0) {
          decreases(i)
          q(i) = fw * iq(i).toDouble
          fw *= twon24
          i -= 1
        }).invariant(
          -1 <= i && i <= jz_1
            && q.length == 20
        )
      }.ensuring(_ =>
        q.length == 20
      )

      loop5()

      // compute PIo2[0,...,jp]*q[jz,...,0]
      @opaque
      def loop6(): Array[Double] = {
        val fq = new Array[Double](20)
        var i = jz_1
        (while (i >= 0) {
          decreases(i)
          val fw = (if 0 <= jz_1 - i then PIo2(0) * q(i + 0) else 0)
            + (if 1 <= jz_1 - i then PIo2(1) * q(i + 1) else 0)
            + (if 2 <= jz_1 - i then PIo2(2) * q(i + 2) else 0)
            + (if 3 <= jz_1 - i then PIo2(3) * q(i + 3) else 0)
            + (if 4 <= jz_1 - i then PIo2(4) * q(i + 4) else 0)
          fq(jz_1 - i) = fw
          i -= 1
        }).invariant(
          -1 <= i && i <= jz_1
            && fq.length == 20
        )
        fq
      }.ensuring(res =>
        res.length == 20
      )

      val fq = loop6()

      val y = {
        // operation order matters here, hence the explicit parentheses
        val fw0 = ((((((((((((((((((fq(19) + fq(18)) + fq(17)) + fq(16)) + fq(15)) + fq(14)) + fq(13)) + fq(12)) + fq(11)) + fq(10)) + fq(9)) + fq(8)) + fq(7)) + fq(6)) + fq(5)) + fq(4)) + fq(3)) + fq(2)) + fq(1)) + fq(0)
        val y0 = if (ih == 0) fw0 else -fw0
        val fw1 = (((((((((((((((((((fq(0) - fw0) + fq(1)) + fq(2)) + fq(3)) + fq(4)) + fq(5)) + fq(6)) + fq(7)) + fq(8)) + fq(9)) + fq(10)) + fq(11)) + fq(12)) + fq(13)) + fq(14)) + fq(15)) + fq(16)) + fq(17)) + fq(18)) + fq(19)
        val y1 = if (ih == 0) fw1 else -fw1
        (y0, y1)
      }
      (n & 7, y)

//      val f = new Array[Double](20)
//      val q = new Array[Double](20)
//
//      {
//        var i = 0
//        (while (i <= jx + jz) {
//          decreases(jx + jz + 1 - i)
//          f(i) = if jv - jx + i < 0 then 0.0d else two_over_pi(i).toDouble
//          i += 1
//        }).invariant(
//          0 <= i && i <= jx + jz + 1
//            && f.length == 20
//            && forall((x: Int) => !(0 <= x && x < i) || f(x) == (if jv - jx + x < 0 then 0.0d else two_over_pi(x).toDouble))
//        )
//      }
//      assert(forall((x: Int) => !(0 <= x && x <= jx + jz) || f(x) == (if jv - jx + x < 0 then 0.0d else two_over_pi(x).toDouble)))
//      {
//        var j = 0
//        (while (j <= jz) {
//          decreases(jz + 1 - j)
//          q(j) = x._1*f(jx + j) + x._2*f(jx + j - 1) + x._3*f(jx + j - 2)
//          j += 1
//        }).invariant(
//          0 <= j && j <= jz + 1
//          && q.length == 20 && f.length == 20
//          && forall((x: Int) => !(0 <= x && x <= jx + jz) || f(x) == (if jv - jx + x < 0 then 0.0d else two_over_pi(x).toDouble))
//          && forall((x: Int) => !(0 <= x && x < j) || q(x).isFinite || !q(x).isFinite)
//        )
//      }

//      (0, (0, 0))
    }

    @ignore @extern
    private def __kernel_rem_pio2_prec_2(x: (Double, Double, Double), e0: Int, nx: Int): (Int, (Double, Double)) = {
//      var jz = 0
      var carry = 0
//      var n = 0
      var i = 0
      var j = 0
      var k = 0
      var m = 0
//      var q0 = 0
//      var ih = 0
      val iq = new Array[Int](20)
      var z = 0.0d
      var fw = 0.0d
      val f = new Array[Double](20)
      val fq = new Array[Double](20)
      val q = new Array[Double](20)

      // initialize jk
      val jk = 4 // init_jk(prec)
      val jp = jk
      val jz = 7

      // determine jx, jv, q0, note that 3 > q0
      val jx = nx - 1
      val jv = {
        val tmp = (e0 - 3) / 24
        if tmp < 0 then 0 else tmp
      }
      val q0 = e0 - 24*(jv + 1);

      // set up f[0] to f[jx+jk] where f[jx+jk] = ipio2[jv+jk]
      j = jv - jx
      m = jx + jz
      i = 0
      while (i <= m) { // max iterations: 7
        f(i) = if (j < 0) 0.0
        else two_over_pi(j).toDouble
        i += 1
        j += 1
      }

      // compute q[0],q[1],...q[jk]
      i = 0
      while (i <= jz) { // max iterations: 4
        fw = 0.0
        if (0 <= jx) {
          fw += x._1 * f(jx + i)
          if (1 <= jx) {
            fw += x._2 * f(jx + i - 1)
            if (2 <= jx) {
              fw += x._3 * f(jx + i - 2)
            }
          }
        }
        q(i) = fw
        i += 1
      }

//      jz = jk
      z = q(jz)
//      n = 0
//      ih = 0
//      var loop = true
//      while (loop) { // max iterations: ????
      // distill q[] into iq[] reversingly
      i = 0
      j = jz
      z = q(jz)
      while (j > 0) { // max iterations: 4
        fw = (twon24 * z).toInt.toDouble
        iq(i) = (z - TWO24 * fw).toInt
        z = q(j - 1) + fw
        i += 1
        j -= 1
      }

      // compute n
      z = OpenJDKMath.scalb(z, q0) // actual value of z
      z -= 8.0 * OpenJDKMath.floor(z * 0.125) // trim off integer >= 8
      val n0 = z.toInt
//      n = z.toInt
      z -= n0.toDouble
//      ih = 0
      val n1 = n0 + (if q0 > 0 then iq(jz - 1) >> (24 - q0) else 0)
      val ih = if (q0 >= 0) {
        i = iq(jz - 1) >> (24 - q0)
        iq(jz - 1) -= i << (24 - q0)
        iq(jz - 1) >> (23 - q0)
      }
      else if (z >= 0.5) 2
      else 0
//      if (q0 > 0) { // need iq[jz - 1] to determine n
//        i = iq(jz - 1) >> (24 - q0)
////        n += i
//        iq(jz - 1) -= i << (24 - q0)
//        ih = iq(jz - 1) >> (23 - q0)
//      }
//      else if (q0 == 0)
//        ih = iq(jz - 1) >> 23
//      else if (z >= 0.5)
//        ih = 2

      val n = n1 + (if ih > 0 then 1 else 0)

      if (ih > 0) { // q > 0.5
//        n += 1
        carry = 0
        i = 0
        while (i < jz) { // compute 1-q // max iterations: 4
          val j = iq(i)
          iq(i) = if carry == 0 then if j != 0 then 0x100_0000 - j else 0 else 0xff_ffff - j
          carry = if carry == 0 && j != 0 then 1 else carry
//          if (carry == 0)
//            if (j != 0) {
//              carry = 1
//              iq(i) = 0x100_0000 - j
//            }
//          else
//            iq(i) = 0xff_ffff - j
          i += 1
        }
        if (q0 > 0) { // rare case: chance is 1 in 12
          q0 match {
            case 1 =>
              iq(jz - 1) &= 0x7f_ffff
            case 2 =>
              iq(jz - 1) &= 0x3f_ffff
          }
        }
        if (ih == 2) {
          z = 1.0 - z
          if (carry != 0)
            z -= OpenJDKMath.scalb(1.0, q0)
        }
      }


//      if (z == 0.0) {
//        j = 0
//        i = jz - 1
//        while (i >= jk) {
//          j |= iq(i)
//          i -= 1
//        }
//        if (j == 0) { // need recomputation
//          k = 1
//          while (iq(jk - k) == 0) { // k = no. of terms needed // max iterations: 4????
//            k += 1
//          }
//          i = jz + 1
//          while (i <= jz + k) { // add q[jz+1] to q[jz+k]
//            f(jx + i) = two_over_pi(jv + i).toDouble
//            j = 0
//            fw = 0.0
//            if (0 <= jx) {
//              fw += x._1 * f(jx + i)
//              if (1 <= jx) {
//                fw += x._2 * f(jx + i - 1)
//                if (2 <= jx) {
//                  fw += x._3 * f(jx + i - 2)
//                }
//              }
//            }
//            q(i) = fw
//            i += 1
//          }
//          jz += k
//        }
//          else
//            loop = false
//        }
//        else
//          loop = false
//      }

      // chop off zero terms
//      if (z == 0.0) {
//        jz -= 1
//        q0 -= 24
//        while (iq(jz) == 0) { // max iterations: 4?
//          jz -= 1
//          q0 -= 24
//        }
//      }
//      else { // break z into 24-bit if necessary
//        z = OpenJDKMath.scalb(z, -q0)
//        if (z >= TWO24) {
//          fw = (twon24 * z).toInt.toDouble
//          iq(jz) = (z - TWO24 * fw).toInt
//          jz += 1
//          q0 += 24
//          iq(jz) = fw.toInt
//        }
//        else
//          iq(jz) = z.toInt
//      }

//      z = OpenJDKMath.scalb(z, -q0)
//      if (z >= TWO24) {
//        fw = (twon24 * z).toInt.toDouble
//        iq(jz) = (z - TWO24 * fw).toInt
//        jz += 1
//        q0 += 24
//        iq(jz) = fw.toInt
//      }
//      else
//        iq(jz) = z.toInt

      z = OpenJDKMath.scalb(z, -q0)
      fw = (twon24 * z).toInt.toDouble
      iq(jz) = (z - TWO24 * fw).toInt
//      jz += 1
//      q0 += 24
      val jz_1 = jz + 1
      val q0_1 = q0 + 24
      iq(jz_1) = fw.toInt

      // convert integer "bit" chunk to floating-point value
      fw = OpenJDKMath.scalb(1.0, q0_1)
      i = jz_1
      while (i >= 0) {
        q(i) = fw * iq(i).toDouble
        fw *= twon24
        i -= 1
      }

      // compute PIo2[0,...,jp]*q[jz,...,0]
      i = jz_1
      while (i >= 0) {
        fw = 0.0
        k = 0
        while (k <= jp && k <= jz_1 - i) {
          fw += PIo2(k) * q(i + k)
          k += 1
        }
        fq(jz_1 - i) = fw
        i -= 1
      }

      val y =  {
        fw = 0.0
        i = jz_1
        while (i >= 0) {
          fw += fq(i)
          i -= 1
        }
        val y0 = if (ih == 0) fw else -fw
        fw = fq(0) - fw
        i = 1
        while (i <= jz) {
          fw += fq(i)
          i += 1
        }
        val y1 = if (ih == 0) fw else -fw
        (y0, y1)
      }
      (n & 7, y)
    }
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
