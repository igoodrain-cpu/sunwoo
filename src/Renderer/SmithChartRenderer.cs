// ════════════════════════════════════════════════════════════════
//  SmithChartRenderer.cs  –  System.Drawing 기반 공용 렌더러
//  WinForms / WPF(WriteableBitmap) / 파일저장(PNG) 모두 지원
// ════════════════════════════════════════════════════════════════
using System;
using System.Collections.Generic;
using System.Drawing;
using System.Drawing.Drawing2D;
using System.Drawing.Text;

namespace Iruza
{
    public class SmithChartStyle
    {
        public int   Margin            { get; set; } = 36;
        public Color BackgroundColor   { get; set; } = Color.FromArgb(245, 248, 255);
        public Color OuterCircleColor  { get; set; } = Color.FromArgb(100, 80, 80, 80);
        public Color RCircleColor      { get; set; } = Color.FromArgb(24, 95, 165);
        public Color XCircleColor      { get; set; } = Color.FromArgb(133, 79, 11);
        public Color VswrCircleColor   { get; set; } = Color.FromArgb(83, 74, 183);
        public Color RealAxisColor     { get; set; } = Color.FromArgb(80, 80, 80);
        public Color LabelColor        { get; set; } = Color.FromArgb(110, 110, 120);
        public Font  LabelFont         { get; set; } = new Font("Arial", 7.5f);
    }

    public class SmithChartRenderer
    {
        private readonly SmithChartCalculator _calc;
        public SmithChartStyle Style { get; set; } = new SmithChartStyle();

        public SmithChartRenderer(SmithChartCalculator calc) => _calc = calc;

        public void Draw(Graphics g, Rectangle bounds,
            IEnumerable<(double Re, double Im, Color Color, string Label)> points = null,
            IEnumerable<(double Re, double Im)> tracePts = null)
        {
            g.SmoothingMode     = SmoothingMode.AntiAlias;
            g.TextRenderingHint = TextRenderingHint.ClearTypeGridFit;

            float cx     = bounds.X + bounds.Width  / 2f;
            float cy     = bounds.Y + bounds.Height / 2f;
            float radius = Math.Min(bounds.Width, bounds.Height) / 2f - Style.Margin;

            PointF Sp(double re, double im)
                => new PointF(cx + (float)(re * radius), cy - (float)(im * radius));

            void ClipDraw(Action act)
            {
                var st = g.Save();
                var gp = new GraphicsPath();
                gp.AddEllipse(cx - radius, cy - radius, radius * 2, radius * 2);
                g.SetClip(gp); act(); g.Restore(st);
            }

            // 배경
            g.FillEllipse(new SolidBrush(Style.BackgroundColor),
                cx - radius, cy - radius, radius * 2, radius * 2);

            // VSWR 기준원
            foreach (double mag in new[] { 0.25, 0.5, 0.75 })
            {
                float r2 = (float)(mag * radius);
                ClipDraw(() => {
                    using var p = new Pen(Color.FromArgb(50, Style.VswrCircleColor), 0.5f)
                                  { DashStyle = DashStyle.Dash };
                    g.DrawEllipse(p, cx - r2, cy - r2, r2 * 2, r2 * 2);
                });
                double v = (1 + mag) / (1 - mag);
                g.DrawString($"{v:F1}", Style.LabelFont,
                    new SolidBrush(Color.FromArgb(120, Style.VswrCircleColor)),
                    cx + r2 + 2, cy - 8);
            }

            // 상수 R 원
            foreach (double rn in new[] { 0.0, 0.5, 1.0, 2.0 })
            {
                float cr = (float)(1.0 / (1 + rn) * radius);
                float ccx = cx + (float)(rn / (1 + rn) * radius);
                bool strong = rn == 0 || rn == 1;
                ClipDraw(() => {
                    using var p = new Pen(
                        Color.FromArgb(strong ? 130 : 55, Style.RCircleColor),
                        strong ? 0.9f : 0.5f);
                    g.DrawEllipse(p, ccx - cr, cy - cr, cr * 2, cr * 2);
                });
                if (rn > 0 && rn <= 2)
                    g.DrawString(rn.ToString(), Style.LabelFont,
                        new SolidBrush(Color.FromArgb(150, Style.RCircleColor)),
                        ccx + cr + 1, cy - 8);
            }

            // 상수 X 아크
            foreach (double xn in new[] { 0.5, 1.0, 2.0 })
            {
                foreach (int sign in new[] { 1, -1 })
                {
                    double xnv = sign * xn;
                    float acx = cx + radius;
                    float acy = cy - (float)(1.0 / xnv * radius);
                    float ar  = (float)(Math.Abs(1.0 / xnv) * radius);
                    bool strong = xn == 1.0;
                    ClipDraw(() => {
                        using var p = new Pen(
                            Color.FromArgb(strong ? 120 : 50, Style.XCircleColor),
                            strong ? 0.9f : 0.5f);
                        g.DrawEllipse(p, acx - ar, acy - ar, ar * 2, ar * 2);
                    });
                }
            }

            // 실수축 & 외곽원
            g.DrawLine(new Pen(Color.FromArgb(80, Style.RealAxisColor), 0.8f),
                cx - radius, cy, cx + radius, cy);
            g.DrawEllipse(new Pen(Color.FromArgb(160, Style.OuterCircleColor), 1.2f),
                cx - radius, cy - radius, radius * 2, radius * 2);

            // 레이블
            var lb = new SolidBrush(Style.LabelColor);
            g.DrawString("SC", Style.LabelFont, lb, cx - radius - 20, cy - 6);
            g.DrawString("OC", Style.LabelFont, lb, cx + radius + 3,  cy - 6);
            g.DrawString("Z₀", Style.LabelFont, lb, cx - 8,           cy - 14);
            g.FillEllipse(lb, cx - 2.5f, cy - 2.5f, 5, 5);

            // 궤적선
            if (tracePts != null)
            {
                var list = new List<(double, double)>(tracePts);
                if (list.Count >= 2)
                {
                    var pts = list.ConvertAll(p => Sp(p.Item1, p.Item2)).ToArray();
                    using var tp = new Pen(Color.FromArgb(70, 100, 150, 200), 1f)
                                   { DashStyle = DashStyle.Dot };
                    g.DrawLines(tp, pts);
                }
            }

            // 임피던스 포인트
            if (points != null)
            {
                foreach (var (re, im, col, lbl) in points)
                {
                    if (re * re + im * im > 1.05) continue;
                    var sp = Sp(re, im);
                    g.FillEllipse(Brushes.White, sp.X - 7, sp.Y - 7, 14, 14);
                    using var br = new SolidBrush(col);
                    g.FillEllipse(br, sp.X - 6, sp.Y - 6, 12, 12);
                    if (!string.IsNullOrEmpty(lbl))
                        g.DrawString(lbl, Style.LabelFont, Brushes.Black, sp.X + 8, sp.Y - 7);
                }
            }
        }

        // PNG 파일 저장
        public void SaveToPng(string path, int w, int h,
            IEnumerable<(double Re, double Im, Color Color, string Label)> points = null,
            IEnumerable<(double Re, double Im)> tracePts = null)
        {
            using var bmp = new Bitmap(w, h);
            using var g   = Graphics.FromImage(bmp);
            g.Clear(Color.White);
            Draw(g, new Rectangle(0, 0, w, h), points, tracePts);
            bmp.Save(path, System.Drawing.Imaging.ImageFormat.Png);
        }
    }
}
