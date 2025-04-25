package stainless
package math

import stainless.annotation.*
import stainless.lang.*

object FdLibm {
  private val TWO24 = 1.67772160000000000000e+07 // 0x1.0p24
  private val EXP_SIGNIF_BITS = 0x7fff_ffff
  private val EXP_BITS = 0x7ff0_0000

  @extern
  private def __LO(x: Double): Int = {
    val transducer = java.lang.Double.doubleToRawLongBits(x)
    transducer.toInt
  }

  @extern
  private def __LO(x: Double, low: Int): Double = {
    val transX = java.lang.Double.doubleToRawLongBits(x)
    java.lang.Double.longBitsToDouble((transX & 0xFFFF_FFFF_0000_0000L) | (low & 0x0000_0000_FFFF_FFFFL))
  }

  @extern
  private def __HI(x: Double): Int = {
    val transducer = java.lang.Double.doubleToRawLongBits(x)
    (transducer >> 32).toInt
  }

  @extern
  private def __HI(x: Double, high: Int): Double = {
    val transX = java.lang.Double.doubleToRawLongBits(x)
    java.lang.Double.longBitsToDouble((transX & 0x0000_0000_FFFF_FFFFL) | high.toLong << 32)
  }

  @extern
  private def __HI_LO(high: Int, low: Int): Double = {
    java.lang.Double.longBitsToDouble((high.toLong << 32) | (low & 0xffff_ffffL))
  }

  object Sin {
    def sin(x: Double): Double = {
      val ix = __HI(x) & EXP_SIGNIF_BITS
      if (ix <= 0x3fe9_21fb) // |x| ~< pi / 4
        __kernel_sin(x, 0.0d, 0)
      else if (ix >= EXP_BITS) // sin(Inf or NaN) is NaN
        x - x
      else {
        val (n, (y0, y1)) = RemPio2.__ieee754_rem_pio2(x)
        n & 3 match {
          case 0 => Sin.__kernel_sin(y0, y1, 1)
          case 1 => Cos.__kernel_cos(y0, y1)
          case 2 => -Sin.__kernel_sin(y0, y1, 1)
          case _ => -Cos.__kernel_cos(y0, y1)
        }
      }
    }

    private val S1 = -1.66666666666666324348e-01d // -0x1.5555555555549p-3
    private val S2 = 8.33333333332248946124e-03d // 0x1.111111110f8a6p-7
    private val S3 = -1.98412698298579493134e-04d // -0x1.a01a019c161d5p-13
    private val S4 = 2.75573137070700676789e-06d // 0x1.71de357b1fe7dp-19
    private val S5 = -2.50507602534068634195e-08d // -0x1.ae5e68a2b9cebp-26
    private val S6 = 1.58969099521155010221e-10d // 0x1.5d93a5acfd57cp-33

    def __kernel_sin(x: Double, y: Double, iy: Int): Double = {
      val ix = __HI(x) & EXP_SIGNIF_BITS
      if (ix < 0x3e40_0000)
        if (x.toInt == 0)
          return x

      val z = x*x
      val v = z*x
      val r = S2 + z*(S3 + z*(S4 + z*(S5 + z*S6)))

      if (iy == 0)
        x + v*(S1 + z*r)
      else
        x - ((z*(0.5d*y - v*r) - y) - v*S1)
    }
  }

  object Cos {
    private val C1 =  4.16666666666666019037e-02d //  0x1.555555555554cp-5
    private val C2 = -1.38888888888741095749e-03d // -0x1.6c16c16c15177p-10
    private val C3 =  2.48015872894767294178e-05d //  0x1.a01a019cb159p-16
    private val C4 = -2.75573143513906633035e-07d // -0x1.27e4f809c52adp-22
    private val C5 =  2.08757232129817482790e-09d //  0x1.1ee9ebdb4b1c4p-29
    private val C6 = -1.13596475577881948265e-11d // -0x1.8fae9be8838d4p-37

    def __kernel_cos(x: Double, y: Double): Double = {
      val ix = __HI(x) & EXP_SIGNIF_BITS
      if (ix < 0x3e40_0000)
        if (x.toInt == 0)
          return 1.0d

      val z = x*x
      val r = z*(C1 + z*(C2 + z*(C3 + z*(C4 + z*(C5 + z*C6)))));
      if (ix < 0x3FD3_3333) // |x| < 0.3
        1.0 - (0.5*z - (z*r - x*y))
      else {
        val qx = if (ix > 0x3fe9_0000) // x > 0.78125
            0.28125d
        else
            __HI_LO(ix - 0x0020_0000, 0)
        val hz = 0.5d*z - qx;
        val a  = 1.0d - qx;
        a - (hz - (z*r - x*y));
      }
    }
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

    def __ieee754_rem_pio2(x: Double): (Int, (Double, Double)) = {
      val hx = __HI(x)
      val ix = hx & EXP_SIGNIF_BITS
      if (ix >= EXP_BITS) { // x is inf or NaN
        (0, (x - x, x - x))
      }
      else if (ix <= 0x3fe9_21fb) { // |x| ~<= pi/4 , no need for reduction
        (0, (x, 0))
      }
      else if (ix < 0x4002_d97c) { // |x| < 3pi/4, special case with n=+-1
        if (hx > 0) { // positive x
          if (ix != 0x3ff9_21fb) { // 33+53 bit pi is good enough
            val z = x - pio2_1
            (1, (z - pio2_1t, (z - (z - pio2_1t)) - pio2_1t))
          } else { // near pi/2, use 33+33+53 bit pi
            val z = (x - pio2_1) - pio2_2
            (1, (z - pio2_2t, (z - (z - pio2_1t)) - pio2_2t))
          }
        } else { // negative x
          if (ix != 0x3ff_921fb) { // 33+53 bit pi is good enough
            val z = x + pio2_1
            (-1, (z + pio2_1t, (z - (z + pio2_1t)) + pio2_1t))
          } else { // near pi/2, use 33+33+53 bit pi
            val z = (x + pio2_1) + pio2_2
            (-1, (z + pio2_2t, (z - (z + pio2_1t)) + pio2_2t))
          }
        }
      }
      else if (ix <= 0x4139_21fb) { // |x| ~<= 2^19*(pi/2), medium size
        val j = ix >> 20
        val abs_x = if x.isNegative then -x else x // Math.abs(x)
        val n = (abs_x * invpio2 + 0.5).toInt
        val fn = n.toDouble
        val r0 = abs_x - fn * pio2_1 // 1st round good to 85 bit
        val w0 = fn * pio2_1t
        val y0 = r0 - w0
        val (yy0, yy1) = if (n < 32 && ix != npio2_hw(n - 1) || ((__HI(y0) >> 20) & 0x7ff) <= 16) {
          (y0, (r0 - y0) - w0)
        } else { // 2nd iteration needed, good to 118
          val r1 = r0 - fn * pio2_2
          val w1 = fn * pio2_2t - ((r0 - r1) - fn * pio2_2)
          val y1 = r1 - w1
          if (j - ((__HI(y1) >> 20) & 0x7ff) <= 49) {
            (y1, (r1 - y1) - w1)
          } else { // 3rd iteration need, 151 bits acc, will cover all possible cases
            val r2 = r1 - fn * pio2_3
            val w2 = fn * pio2_3t - ((r1 - r2) - fn * pio2_3)
            val y2 = r2 - w2
            (y2, (r2 - y2) - w2)
          }
        }
        if hx < 0 then (-n, (-yy0, -yy1)) else (n, (yy0, yy1))
      }
      else { // all other (large) arguments
        // set z = scalbn(|x|, ilogb(x)-23)
        val z0 = __LO(0.0d, __LO(x))
        val e0 = (ix >> 20) - 1046 // e0 = ilogb(z) - 23;
        val z1 = __HI(z0, ix - (e0 << 20))
        val tx0 = z1.toInt.toDouble
        val z2 = (z1 - tx0) * TWO24
        val tx1 = z2.toInt.toDouble
        val z3 = (z2 - tx1) * TWO24
        val tx2 = z3
        val nx = if tx2 == 0.0 then if tx1 == 0.0 then if tx0 == 0.0 then 0 else 1 else 2 else 3
        val (n1, (y0, y1)) = KernelRemPio2.__kernel_rem_pio2_prec_2((tx0, tx1, tx2), e0, nx)
        if hx < 0 then (-n1, (-y0, -y1)) else (n1, (y0, y1))
      }
    }
  }

  @extern
  object KernelRemPio2 {
//    private val init_jk = Array[Int](2, 3, 4, 6)

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

    def __kernel_rem_pio2_prec_2(x: (Double, Double, Double), e0: Int, nx: Int): (Int, (Double, Double)) = {
      var jz = 0
      var carry = 0
      var n = 0
      var i = 0
      var j = 0
      var k = 0
      var m = 0
      var q0 = 0
      var ih = 0
      val iq = new Array[Int](20)
      var z = 0.0d
      var fw = 0.0d
      val f = new Array[Double](20)
      val fq = new Array[Double](20)
      val q = new Array[Double](20)

      // initialize jk
      val jk = 4 // init_jk(prec)
      val jp = jk

      // determine jx, jv, q0, note that 3 > q0
      val jx = nx - 1
      val jv = {
        val tmp = (e0 - 3) / 24
        if tmp < 0 then 0 else tmp
      }
      q0 = e0 - 24*(jv + 1);

      // set up f[0] to f[jx+jk] where f[jx+jk] = ipio2[jv+jk]
      j = jv - jx
      m = jx + jk
      i = 0
      while (i <= m) { // max iterations: 7
        f(i) = if (j < 0) 0.0
        else two_over_pi(j).toDouble
        i += 1
        j += 1
      }

      // compute q[0],q[1],...q[jk]
      i = 0
      while (i <= jk) { // max iterations: 4
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

      jz = jk
      z = q(jz)
      n = 0
      ih = 0
      var loop = true
      while (loop) { // max iterations: ????
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
        z = Math.scalb(z, q0) // actual value of z
        z -= 8.0 * Math.floor(z * 0.125) // trim off integer >= 8
        n = z.toInt
        z -= n.toDouble
        ih = 0
        if (q0 > 0) { // need iq[jz - 1] to determine n
          i = iq(jz - 1) >> (24 - q0)
          n += i
          iq(jz - 1) -= i << (24 - q0)
          ih = iq(jz - 1) >> (23 - q0)
        }
        else if (q0 == 0)
          ih = iq(jz - 1) >> 23
        else if (z >= 0.5)
          ih = 2

        if (ih > 0) { // q > 0.5
          n += 1
          carry = 0
          i = 0
          while (i < jz) { // compute 1-q // max iterations: 4
            j = iq(i)
            if (carry == 0)
              if (j != 0) {
                carry = 1
                iq(i) = 0x100_0000 - j
              }
            else
              iq(i) = 0xff_ffff - j
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
              z -= Math.scalb(1.0, q0)
          }
        }

        if (z == 0.0) {
          j = 0
          i = jz - 1
          while (i >= jk) {
            j |= iq(i)
            i -= 1
          }
          if (j == 0) { // need recomputation
            k = 1
            while (iq(jk - k) == 0) { // k = no. of terms needed // max iterations: 4????
              k += 1
            }
            i = jz + 1
            while (i <= jz + k) { // add q[jz+1] to q[jz+k]
              f(jx + i) = two_over_pi(jv + i).toDouble
              j = 0
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
            jz += k
          }
          else
            loop = false
        }
        else
          loop = false
      }

      // chop off zero terms
      if (z == 0.0) {
        jz -= 1
        q0 -= 24
        while (iq(jz) == 0) { // max iterations: 4?
          jz -= 1
          q0 -= 24
        }
      }
      else { // break z into 24-bit if necessary
        z = Math.scalb(z, -q0)
        if (z >= TWO24) {
          fw = (twon24 * z).toInt.toDouble
          iq(jz) = (z - TWO24 * fw).toInt
          jz += 1
          q0 += 24
          iq(jz) = fw.toInt
        }
        else
          iq(jz) = z.toInt
      }

      // convert integer "bit" chunk to floating-point value
      fw = Math.scalb(1.0, q0)
      i = jz
      while (i >= 0) { // max iterations: 4?
        q(i) = fw * iq(i).toDouble
        fw *= twon24
        i -= 1
      }

      // compute PIo2[0,...,jp]*q[jz,...,0]
      i = jz
      while (i >= 0) { // max iterations: 4?
        fw = 0.0
        k = 0
        while (k <= jp && k <= jz - i) {
          fw += PIo2(k) * q(i + k)
          k += 1
        }
        fq(jz - i) = fw
        i -= 1
      }

      val y1 =  {
        fw = 0.0
        i = jz
        while (i >= 0) { // max iterations: 4?
          fw += fq(i)
          i -= 1
        }
        val y10 = if (ih == 0) fw else -fw
        fw = fq(0) - fw
        i = 1
        while (i <= jz) { // max iterations: 4?
          fw += fq(i)
          i += 1
        }
        val y11 = if (ih == 0) fw else -fw
        (y10, y11)
      }
      (n & 7, y1)
    }
  }

  @ignore
  def main(argv: Array[String]): Unit = {
    Sin.sin(9.061448382195477E-155)
    var i = Int.MinValue
    while (i != Int.MaxValue) {
      val d = java.lang.Float.intBitsToFloat(i).toDouble
      if (i % 100000000 == 0)
        println(s"progress: $d")
      val s1 = Sin.sin(d)
      val s2 = Math.sin(d)
      val diff = Math.abs(s1 - s2)
      val ulp = Math.min(Math.ulp(s1), Math.ulp(s2))
      if diff > ulp  then {
        println(s"error: d = $d, diff = $diff, s1 = $s1, s2 = $s2, ulp(s1) = ${Math.ulp(s1)}, ulp(s2r) = ${Math.ulp(s2)}")
        i = Int.MaxValue
      }
      else
        i += 1
    }
  }
}
