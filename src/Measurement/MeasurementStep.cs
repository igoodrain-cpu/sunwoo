// ════════════════════════════════════════════════════════════════
//  MeasurementStep.cs  –  측정 스텝 데이터 모델 (15 컬럼)
//  컬럼: Step, Vout, Iout, Phase, R, X, Γr, Γi, |Γ|, VSWR,
//         Z text, z normalized, Fwd P, Ref P, Del P
// ════════════════════════════════════════════════════════════════
using System;
using System.Numerics;

namespace Iruza
{
    public class MeasurementStep
    {
        // ── 원시 측정값 ──
        public int    Step         { get; set; }
        public double Vout_Vrms    { get; set; }
        public double Iout_Arms    { get; set; }
        public double Phase_deg    { get; set; }

        // ── 임피던스 ──
        public double R            { get; set; }
        public double X            { get; set; }

        // ── 반사계수 ──
        public double Gamma_Real   { get; set; }
        public double Gamma_Imag   { get; set; }

        // ── 계산값 ──
        public double VSWR         { get; set; }
        public string Z_Text       { get; set; } = "";
        public string Z_Normalized { get; set; } = "";

        // ── 전력 ──
        public double ForwardP_W   { get; set; }
        public double ReflectedP_W { get; set; }
        public double DeliveredP_W { get; set; }

        // ── 파생 프로퍼티 (저장 불필요) ──
        public double GammaMag     => Math.Sqrt(Gamma_Real * Gamma_Real + Gamma_Imag * Gamma_Imag);
        public double Phase_rad    => Phase_deg * Math.PI / 180.0;
        public double ReturnLoss_dB => GammaMag < 1e-10 ? 100.0 : -20.0 * Math.Log10(GammaMag);
        public double Efficiency_pct => ForwardP_W > 1e-12 ? DeliveredP_W / ForwardP_W * 100.0 : 0.0;
        public Complex Gamma       => new Complex(Gamma_Real, Gamma_Imag);

        // ── V/I/θ → Z → Γ 자동 계산 ──
        public void ComputeFromVI(double z0 = 50.0)
        {
            if (Iout_Arms < 1e-12) { R = 0; X = 0; }
            else
            {
                double zm = Vout_Vrms / Iout_Arms;
                R = Math.Max(0, zm * Math.Cos(Phase_rad));
                X = zm * Math.Sin(Phase_rad);
                DeliveredP_W = Vout_Vrms * Iout_Arms * Math.Cos(Phase_rad);
            }
            ComputeFromZ(z0);
            double m2 = GammaMag * GammaMag;
            if (ForwardP_W < 1e-9) ForwardP_W = DeliveredP_W / Math.Max(1 - m2, 0.001);
            ReflectedP_W = ForwardP_W * m2;
        }

        // ── R/X → Γ → VSWR 자동 계산 ──
        public void ComputeFromZ(double z0 = 50.0)
        {
            double rn = R / z0, xn = X / z0;
            double denom = (rn + 1) * (rn + 1) + xn * xn;
            if (denom < 1e-12) { Gamma_Real = 1; Gamma_Imag = 0; }
            else
            {
                Gamma_Real = ((rn - 1) * (rn + 1) + xn * xn) / denom;
                Gamma_Imag = 2 * xn / denom;
            }
            double mag = GammaMag;
            VSWR = mag >= 1.0 ? 99.9 : (1 + mag) / (1 - mag);
            string xs = X >= 0 ? "+" : "";
            Z_Text       = $"{R:F2}{xs}j{X:F2}Ω";
            Z_Normalized = $"{rn:F3}{xs}j{xn:F3}";
        }
    }
}
