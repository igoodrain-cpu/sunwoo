// ════════════════════════════════════════════════════════════════
//  PlasmaFingerprintPanel.cs  –  탭1: Plasma Fingerprint 분석 탭
//  이미지 레이아웃: 스미스차트(좌) + 4가지 패턴 카드(우) + 하단 바
// ════════════════════════════════════════════════════════════════
using System;
using System.Drawing;
using System.Drawing.Drawing2D;
using System.Drawing.Text;
using System.Linq;
using System.Windows.Forms;

namespace Iruza
{
    public class PlasmaFingerprintPanel : Panel
    {
        private FingerprintMode   _active = FingerprintMode.Normal;
        private SmithChartDrawPanel _chartDraw;
        private Label             _statusLbl;
        private Button[]          _cardBtns;

        public PlasmaFingerprintPanel()
        {
            Padding     = new Padding(16);
            BackColor   = Color.White;
            BuildLayout();
        }

        void BuildLayout()
        {
            var titleLbl = new Label
            {
                Text = "Smith Chart 기반 Plasma Fingerprint 분석 개념",
                Font = new Font("Malgun Gothic", 13f, FontStyle.Bold),
                ForeColor = Color.FromArgb(25, 25, 50),
                Dock = DockStyle.Top, Height = 30, Padding = new Padding(0,4,0,0)
            };
            var titleLine = new Panel { Dock=DockStyle.Top, Height=1, BackColor=Color.FromArgb(180,180,205) };

            // ── 본문 레이아웃 ──
            var body = new TableLayoutPanel
            {
                Dock=DockStyle.Fill, ColumnCount=2, RowCount=1
            };
           // body.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 48));
           // body.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 52));

            body.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 68));   // [CHG] 차트 영역 확대 (48→68)
            body.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 32));   // [CHG] 카드 영역 축소 (52→32)




            // 좌측: 차트
            var leftPanel = new Panel { Dock=DockStyle.Fill };
            _chartDraw = new SmithChartDrawPanel { Dock=DockStyle.Fill };
            _chartDraw.HoverChanged += info => _statusLbl.Text =
                string.IsNullOrEmpty(info) ? "포인트에 마우스를 올리면 임피던스 정보가 표시됩니다." : info;

            var chartTitle = new Label
            {
                Text="Smith Chart Fingerprint", Dock=DockStyle.Top, Height=24,
                Font=new Font("Malgun Gothic",9.5f,FontStyle.Bold),
                ForeColor=Color.FromArgb(40,80,120), TextAlign=ContentAlignment.MiddleCenter
            };
            leftPanel.Controls.Add(_chartDraw);
            leftPanel.Controls.Add(chartTitle);

            var chartSub = new Label
            {
                Text="정상 경로 / Drift·Mismatch 경향 비교",
                Dock=DockStyle.Bottom, Height=20,
                Font=new Font("Malgun Gothic",8f), ForeColor=Color.FromArgb(120,120,140),
                TextAlign=ContentAlignment.MiddleCenter
            };
            leftPanel.Controls.Add(chartSub);

            body.Controls.Add(leftPanel, 0, 0);

            // 우측: 패턴 카드
            var rightPanel = new Panel { Dock=DockStyle.Fill, Padding=new Padding(8,0,0,0) };
            _cardBtns = new Button[4];
            var patterns = FingerprintLibrary.All;

            const int CARD_H = 64;    // [CHG] 카드 높이 축소 (88→64)
            const int CARD_GAP = 72;    // [CHG] 카드 간격 축소 (96→72)


            int initW = Math.Max(rightPanel.Width, 260) - 8;   // [CHG] 레이아웃 전 Width=0 방지

            for (int i = 0; i < patterns.Count; i++)
            {
                var pat = patterns[i];
                var idx = i;
                var btn = new Button
                {
                    FlatStyle   = FlatStyle.Flat,
                    BackColor   = pat.FillColor,
                    Cursor      = Cursors.Hand,
                    Text        = "",
                    //Size        = new Size(rightPanel.Width - 8, 88),
                    //Location    = new Point(0, i * 96),
                    Size = new Size(initW, CARD_H),
                    Location = new Point(0, i * CARD_GAP),
                    Anchor      = AnchorStyles.Top | AnchorStyles.Left | AnchorStyles.Right
                };
                btn.FlatAppearance.BorderColor   = pat.BorderColor;
                btn.FlatAppearance.BorderSize    = 1;
                btn.FlatAppearance.MouseDownBackColor = pat.FillColor;
                btn.FlatAppearance.MouseOverBackColor = ControlPaint.Light(pat.FillColor, 0.2f);

                // 카드 내부 레이블
                var lTitle = new Label
                {
                    Text=pat.Label, AutoSize=false, //Height=22,
                    Height = 18,
                    Font = new Font("Malgun Gothic", 9.5f, FontStyle.Bold),   // [CHG] 10.5→9.5
                    ForeColor = pat.TitleColor,
                    BackColor = Color.Transparent,
                    Location = new Point(8, 6),
                    Width = initW - 16,
                    Anchor = AnchorStyles.Top | AnchorStyles.Left | AnchorStyles.Right

                   // Font =new Font("Malgun Gothic",10.5f,FontStyle.Bold),
                   // ForeColor=pat.TitleColor, BackColor=Color.Transparent,
                   // Location=new Point(10,8), Width=300
                };
                var lBody = new Label
                {
                    Text=pat.Subtitle, AutoSize=false, //Height=44,
                    Height = 36,
                    Font = new Font("Malgun Gothic", 8f),                    // [CHG] 8.5→8
                    ForeColor = pat.BodyColor,
                    BackColor = Color.Transparent,
                    Location = new Point(8, 26),
                    Width = initW - 16,
                    Anchor = AnchorStyles.Top | AnchorStyles.Left | AnchorStyles.Right

                   //Font =new Font("Malgun Gothic",8.5f),
                    //ForeColor=pat.BodyColor, BackColor=Color.Transparent,
                    //Location=new Point(10,32), Width=300
                };
                btn.Controls.Add(lTitle);
                btn.Controls.Add(lBody);

                foreach (Control c in btn.Controls)
                    c.Click += (s,e) => ActivateMode(pat.Mode);
                btn.Click += (s,e) => ActivateMode(pat.Mode);

                rightPanel.Controls.Add(btn);
                _cardBtns[i] = btn;
            }

            rightPanel.Resize += (s,e) =>
            {
                for (int i=0;i<_cardBtns.Length;i++)
                //    _cardBtns[i].Width = rightPanel.Width - 8;
                _cardBtns[i].Width = Math.Max(rightPanel.Width - 8, 120);   // [CHG] 0/음수 폭 방지
            };

            body.Controls.Add(rightPanel, 1, 0);

            // 상태 레이블
            _statusLbl = new Label
            {
                Text="포인트에 마우스를 올리면 임피던스 정보가 표시됩니다.",
                Dock=DockStyle.Bottom, Height=22,
                Font=new Font("Consolas",8.5f), ForeColor=Color.FromArgb(80,80,100)
            };

            // 하단 바
            var bottomBar = new Panel
            {
                Dock=DockStyle.Bottom, Height=46,
                BackColor=Color.FromArgb(230,241,251),
                Padding=new Padding(12,0,12,0)
            };
            bottomBar.Paint += (s,e) =>
                e.Graphics.DrawRectangle(new Pen(Color.FromArgb(133,183,235)),
                    0,0,((Panel)s).Width-1,((Panel)s).Height-1);
            var bottomLbl = new Label
            {
                Text="동일 조건 Power Data별 Fingerprint 추세선을 비교하여 정상 패턴 인자를 기록하고 표준 Rule 수립에 활용",
                Dock=DockStyle.Fill, TextAlign=ContentAlignment.MiddleCenter,
                Font=new Font("Malgun Gothic",8.5f), ForeColor=Color.FromArgb(12,68,124)
            };
            bottomBar.Controls.Add(bottomLbl);

            Controls.Add(body);
            Controls.Add(titleLine);
            Controls.Add(titleLbl);
            Controls.Add(_statusLbl);
            Controls.Add(bottomBar);

            ActivateMode(FingerprintMode.Normal);
        }

        void ActivateMode(FingerprintMode mode)
        {
            _active = mode;
            _chartDraw.SetMode(mode);

            var patterns = FingerprintLibrary.All;
            for (int i = 0; i < _cardBtns.Length; i++)
            {
                bool on = patterns[i].Mode == mode;
                _cardBtns[i].FlatAppearance.BorderSize = on ? 2 : 1;
            }
        }
    }

    // ── 내부 차트 그리기 패널 ──
    public class SmithChartDrawPanel : Control
    {
        private FingerprintMode _mode = FingerprintMode.Normal;
        private (double Re, double Im)? _hover;
        public event Action<string> HoverChanged;

        public SmithChartDrawPanel()
        {
            DoubleBuffered = true; ResizeRedraw = true;
            SetStyle(ControlStyles.OptimizedDoubleBuffer |
                     ControlStyles.AllPaintingInWmPaint | ControlStyles.UserPaint, true);
        }

        public void SetMode(FingerprintMode m) { _mode = m; Invalidate(); }

        PointF Sp(double re, double im, float cx, float cy, float r)
            => new PointF(cx + (float)(re*r), cy - (float)(im*r));

        void ClipDraw(Graphics g, float cx, float cy, float rad, Action act)
        {
            var st = g.Save();
            var gp = new GraphicsPath();
            gp.AddEllipse(cx-rad, cy-rad, rad*2, rad*2);
            g.SetClip(gp); act(); g.Restore(st);
        }

        protected override void OnPaint(PaintEventArgs e)
        {
            base.OnPaint(e);
            var g = e.Graphics;
            g.SmoothingMode     = SmoothingMode.AntiAlias;
            g.TextRenderingHint = TextRenderingHint.ClearTypeGridFit;

            float cx = Width/2f, cy = Height/2f;
            float rad = Math.Min(cx, cy) - 28;

            DrawGrid(g, cx, cy, rad);
            DrawNormalTrace(g, cx, cy, rad);
            if (_mode != FingerprintMode.Normal)
                DrawAnomalyTrace(g, cx, cy, rad);

            if (_hover.HasValue)
            {
                var sp = Sp(_hover.Value.Re, _hover.Value.Im, cx, cy, rad);
                g.DrawEllipse(new Pen(Color.Black, 1.5f), sp.X-10, sp.Y-10, 20, 20);
            }
        }

        void DrawGrid(Graphics g, float cx, float cy, float rad)
        {
            g.FillEllipse(new SolidBrush(Color.FromArgb(245,248,255)),
                cx-rad, cy-rad, rad*2, rad*2);

            foreach (double mag in new[]{0.25, 0.5, 0.75})
            {
                float r2 = (float)(mag*rad);
                ClipDraw(g,cx,cy,rad,()=>{
                    using var p = new Pen(Color.FromArgb(45,83,74,183),0.5f){DashStyle=DashStyle.Dash};
                    g.DrawEllipse(p,cx-r2,cy-r2,r2*2,r2*2);
                });
            }
            foreach (double rn in new[]{0.0,0.5,1.0,2.0})
            {
                float cr=(float)(1.0/(1+rn)*rad), ccx=cx+(float)(rn/(1+rn)*rad);
                bool st=(rn==0||rn==1);
                ClipDraw(g,cx,cy,rad,()=>{
                    using var p=new Pen(Color.FromArgb(st?130:50,24,95,165),st?.9f:.5f);
                    g.DrawEllipse(p,ccx-cr,cy-cr,cr*2,cr*2);
                });
            }
            foreach (double xn in new[]{0.5,1.0,2.0})
                foreach (int sign in new[]{1,-1})
                {
                    double xnv=sign*xn;
                    float acx=cx+rad, acy=cy-(float)(1.0/xnv*rad), ar=(float)(Math.Abs(1.0/xnv)*rad);
                    bool st=(xn==1.0);
                    ClipDraw(g,cx,cy,rad,()=>{
                        using var p=new Pen(Color.FromArgb(st?120:45,133,79,11),st?.9f:.5f);
                        g.DrawEllipse(p,acx-ar,acy-ar,ar*2,ar*2);
                    });
                }

            g.DrawLine(new Pen(Color.FromArgb(70,80,80,80),.8f), cx-rad,cy, cx+rad,cy);
            g.DrawEllipse(new Pen(Color.FromArgb(150,80,80,80),1.2f), cx-rad,cy-rad,rad*2,rad*2);

            var lf = new Font("Arial",7.5f);
            var lb = new SolidBrush(Color.FromArgb(130,90,90,90));
            g.DrawString("SC",lf,lb, cx-rad-20, cy-6);
            g.DrawString("OC",lf,lb, cx+rad+3,  cy-6);
            g.DrawString("Z₀",lf,lb, cx-8,      cy-14);
            g.FillEllipse(lb, cx-2.5f,cy-2.5f,5,5);
        }

        void DrawTrace(Graphics g, FingerprintPattern pat, float cx, float cy, float rad, bool dash)
        {
            if (pat.Points.Count < 2) return;
            var pts = pat.Points.Select(p => Sp(p.Re, p.Im, cx, cy, rad)).ToArray();

            using var pen = new Pen(pat.TraceColor, 1.8f);
            if (dash) pen.DashStyle = DashStyle.Dash;
            g.DrawLines(pen, pts);

            foreach (var (sp, i) in pts.Select((p,i)=>(p,i)))
            {
                g.FillEllipse(Brushes.White, sp.X-6.5f, sp.Y-6.5f, 13, 13);
                using var br = new SolidBrush(pat.TraceColor);
                g.FillEllipse(br, sp.X-5, sp.Y-5, 10, 10);
                if (i == pts.Length - 1)
                    g.DrawEllipse(new Pen(pat.TraceColor, 1.2f), sp.X-7, sp.Y-7, 14, 14);
            }
        }

        void DrawNormalTrace(Graphics g, float cx, float cy, float rad)
            => DrawTrace(g, FingerprintLibrary.Normal, cx, cy, rad, false);

        void DrawAnomalyTrace(Graphics g, float cx, float cy, float rad)
            => DrawTrace(g, FingerprintLibrary.Get(_mode), cx, cy, rad, true);

        protected override void OnMouseMove(MouseEventArgs e)
        {
            base.OnMouseMove(e);
            float cx=Width/2f, cy=Height/2f, rad=Math.Min(cx,cy)-28;

            var all = FingerprintLibrary.Normal.Points.ToList();
            if (_mode != FingerprintMode.Normal)
                all.AddRange(FingerprintLibrary.Get(_mode).Points);

            (double Re, double Im)? best = null; double bestD = 15*15;
            foreach (var p in all)
            {
                var sp = Sp(p.Re, p.Im, cx, cy, rad);
                double d = Math.Pow(e.X-sp.X,2) + Math.Pow(e.Y-sp.Y,2);
                if (d < bestD) { bestD=d; best=p; }
            }

            _hover = best;
            Cursor = best.HasValue ? Cursors.Hand : Cursors.Default;

            if (best.HasValue)
            {
                var (re, im) = best.Value;
                double mag = Math.Sqrt(re*re+im*im);
                double vswr = mag>=1?99.9:(1+mag)/(1-mag);
                double rl   = mag<1e-10?100:-20*Math.Log10(mag);
                double d2   = (1-re)*(1-re)+im*im;
                double rn   = d2<1e-10?1e6:(1-re*re-im*im)/d2;
                double xn   = d2<1e-10?0:2*im/d2;
                string xs   = xn>=0?"+":" ";
                HoverChanged?.Invoke($"Z = {rn*50:F1}{xs}j{xn*50:F1} Ω  |Γ| = {mag:F4}  VSWR = {vswr:F2}  RL = {rl:F1} dB");
            }
            else HoverChanged?.Invoke("");

            Invalidate();
        }

        protected override void OnMouseLeave(EventArgs e)
        {
            base.OnMouseLeave(e); _hover=null;
            HoverChanged?.Invoke(""); Invalidate();
        }
    }
}
