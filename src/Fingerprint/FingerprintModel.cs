// ════════════════════════════════════════════════════════════════
//  FingerprintModel.cs  –  Plasma Fingerprint 패턴 데이터 모델
// ════════════════════════════════════════════════════════════════
using System;
using System.Collections.Generic;
using System.Drawing;
using System.Linq;

namespace Iruza
{
    public enum FingerprintMode { Normal, Matching, ChamberDrift, ArcPrecursor }

    public class FingerprintPattern
    {
        public FingerprintMode Mode        { get; }
        public string          Label       { get; }
        public string          Subtitle    { get; }
        public Color           TraceColor  { get; }
        public Color           BorderColor { get; }
        public Color           FillColor   { get; }
        public Color           TitleColor  { get; }
        public Color           BodyColor   { get; }
        public IReadOnlyList<(double Re, double Im)> Points { get; }

        public FingerprintPattern(FingerprintMode mode, string label, string subtitle,
            Color traceColor, Color borderColor, Color fillColor,
            Color titleColor, Color bodyColor,
            IEnumerable<(double, double)> pts)
        {
            Mode = mode; Label = label; Subtitle = subtitle;
            TraceColor = traceColor; BorderColor = borderColor; FillColor = fillColor;
            TitleColor = titleColor; BodyColor = bodyColor;
            Points = new List<(double, double)>(pts);
        }

        public double PeakGammaMag()
        {
            if (!Points.Any()) return 0;
            return Points.Max(p => Math.Sqrt(p.Re * p.Re + p.Im * p.Im));
        }
    }

    public static class FingerprintLibrary
    {
        public static readonly IReadOnlyList<FingerprintPattern> All = BuildAll();

        static IReadOnlyList<FingerprintPattern> BuildAll()
        {
            var normal = new (double,double)[]
            {
                (-0.35, 0.28),(-0.28, 0.20),(-0.18, 0.14),
                (-0.06, 0.08),( 0.04, 0.04),( 0.08, 0.00)
            };
            var matching = new (double,double)[]
            {
                (0.08,0.00),(0.18,0.12),(0.30,0.28),(0.40,0.40),(0.46,0.50)
            };
            var drift = new (double,double)[]
            {
                (0.08,0.00),(0.10,-0.08),(0.16,-0.18),(0.22,-0.28),(0.28,-0.36),(0.32,-0.42)
            };
            var arc = new (double,double)[]
            {
                (0.08,0.00),(0.22,0.08),(0.48,0.22),(0.60,0.50),(0.55,0.62)
            };

            return new[]
            {
                new FingerprintPattern(FingerprintMode.Normal,
                    "정상 패턴",
                    "동일 Recipe·Power 조건에서\nR-X 궤적이 정상 영역 내 반복",
                    Color.FromArgb(15,110,86), Color.FromArgb(93,202,165),
                    Color.FromArgb(225,245,238), Color.FromArgb(8,80,65), Color.FromArgb(15,110,86),
                    normal),
                new FingerprintPattern(FingerprintMode.Matching,
                    "Matching 이상",
                    "VSWR 증가, Gamma 변화,\nLoad/Tune 한계 접근",
                    Color.FromArgb(216,90,48), Color.FromArgb(239,159,39),
                    Color.FromArgb(250,238,218), Color.FromArgb(65,36,2), Color.FromArgb(99,56,6),
                    matching),
                new FingerprintPattern(FingerprintMode.ChamberDrift,
                    "Chamber Drift",
                    "벽면 상태 변화, Deposit 영향으로\nBaseline이 서서히 이동",
                    Color.FromArgb(55,138,221), Color.FromArgb(133,183,235),
                    Color.FromArgb(230,241,251), Color.FromArgb(4,44,83), Color.FromArgb(12,68,124),
                    drift),
                new FingerprintPattern(FingerprintMode.ArcPrecursor,
                    "Arc 발생 전조",
                    "Voltage Spike, Phase Jump,\nReflect 급증 패턴 확인",
                    Color.FromArgb(226,75,74), Color.FromArgb(240,149,149),
                    Color.FromArgb(252,235,235), Color.FromArgb(80,19,19), Color.FromArgb(121,31,31),
                    arc),
            };
        }

        public static FingerprintPattern Get(FingerprintMode mode)
            => All.First(p => p.Mode == mode);

        public static FingerprintPattern Normal => Get(FingerprintMode.Normal);
    }
}
