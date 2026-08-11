// ════════════════════════════════════════════════════════════════
//  SmithChartCalculator.cs  –  핵심 RF 계산 엔진
//  반사계수, VSWR, 반사손실, L/C 매칭 소자, λ/4 변환기
// ════════════════════════════════════════════════════════════════
using System;
using System.Numerics;

namespace Iruza
{
    public class SmithChartCalculator
    {
        public double Z0 { get; set; } = 50.0;

        public Complex ImpedanceToGamma(double r, double x)
        {
            var zn = new Complex(r / Z0, x / Z0);
            var denom = zn + Complex.One;
            if (denom.Magnitude < 1e-12) return new Complex(1, 0);
            return (zn - Complex.One) / denom;
        }

        public (double R, double X) GammaToImpedance(Complex gamma)
        {
            var denom = Complex.One - gamma;
            if (denom.Magnitude < 1e-12) return (1e6, 0);
            var zn = (Complex.One + gamma) / denom;
            return (zn.Real * Z0, zn.Imaginary * Z0);
        }

        public double CalcVSWR(Complex gamma)
        {
            double m = gamma.Magnitude;
            return m >= 1.0 ? 99.9 : (1 + m) / (1 - m);
        }

        public double CalcReturnLoss(Complex gamma)
        {
            double m = gamma.Magnitude;
            return m < 1e-10 ? 100.0 : -20 * Math.Log10(m);
        }

        public double CalcMismatchLoss(Complex gamma)
            => -10 * Math.Log10(1 - gamma.Magnitude * gamma.Magnitude);

        public double CalcDeliveredPower(Complex gamma, double forwardPower)
            => forwardPower * (1 - gamma.Magnitude * gamma.Magnitude);

        public (double R, double X) ApplySeriesL(double r, double x, double L_nH, double freq_MHz)
        {
            double omega = 2 * Math.PI * freq_MHz * 1e6;
            return (r, x + omega * L_nH * 1e-9);
        }

        public (double R, double X) ApplySeriesC(double r, double x, double C_pF, double freq_MHz)
        {
            double omega = 2 * Math.PI * freq_MHz * 1e6;
            return (r, x - 1.0 / (omega * C_pF * 1e-12));
        }

        public (double R, double X) ApplyShuntL(double r, double x, double L_nH, double freq_MHz)
        {
            double omega = 2 * Math.PI * freq_MHz * 1e6;
            double rr = r * r + x * x;
            if (rr < 1e-12) return (r, x);
            double g = r / rr, b = -x / rr;
            double b2 = b - 1.0 / (omega * L_nH * 1e-9) / Z0;
            double d  = g * g + b2 * b2;
            return d < 1e-12 ? (r, x) : (g / d * Z0, -b2 / d * Z0);
        }

        public (double R, double X) ApplyShuntC(double r, double x, double C_pF, double freq_MHz)
        {
            double omega = 2 * Math.PI * freq_MHz * 1e6;
            double rr = r * r + x * x;
            if (rr < 1e-12) return (r, x);
            double g = r / rr, b = -x / rr;
            double b2 = b + omega * C_pF * 1e-12 * Z0;
            double d  = g * g + b2 * b2;
            return d < 1e-12 ? (r, x) : (g / d * Z0, -b2 / d * Z0);
        }

        public double QuarterWaveTransformer(double zSource, double zLoad)
            => Math.Sqrt(zSource * zLoad);

        public (double L_series_nH, double C_shunt_pF, double C_series_pF, double L_shunt_nH)
            LNetworkMatch(double rSource, double rLoad, double freq_MHz)
        {
            double omega = 2 * Math.PI * freq_MHz * 1e6;
            double Q  = Math.Sqrt(rLoad / rSource - 1);
            double xs = rLoad / Q, xp = rSource * Q;
            return (xs / omega * 1e9, 1.0 / (omega * xp) * 1e12,
                    1.0 / (omega * xs) * 1e12, xp / omega * 1e9);
        }

        public (double stubLen_deg, double lineLen_deg) SingleStubMatch(double r, double x)
        {
            var zn  = new Complex(r / Z0, x / Z0);
            double m2 = zn.Real * zn.Real + zn.Imaginary * zn.Imaginary;
            if (m2 < 1e-12) return (0, 0);
            double g = zn.Real / m2, b = -zn.Imaginary / m2;
            double bStub   = -b + (g >= 1 ? Math.Sqrt(g * (g - 1)) : 0);
            double lineLen = Math.Abs(Math.Atan2(bStub - b, g - 1) * 90 / Math.PI);
            double stubLen = Math.Abs(Math.Atan(bStub) * 180 / Math.PI);
            return (stubLen, lineLen);
        }
    }
}
