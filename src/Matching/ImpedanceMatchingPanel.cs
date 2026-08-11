// ════════════════════════════════════════════════════════════════
//  ImpedanceMatchingPanel.cs  –  탭3: RF 임피던스 매칭 계산기
//  L-network / λ/4 변환기 / 단일 스텁 / 직렬·병렬 소자 시각화
// ════════════════════════════════════════════════════════════════
using System;
using System.Drawing;
using System.Drawing.Drawing2D;
using System.Drawing.Text;
using System.Linq;
using System.Windows.Forms;

namespace Iruza
{
    public class ImpedanceMatchingPanel : Panel
    {
        private readonly SmithChartCalculator _calc = new SmithChartCalculator { Z0=50 };
        private MatchingChartPanel _chart;
        private Label   _resultLbl;
        private NumericUpDown _nR,_nX,_nZ0,_nFreq,_nVal;
        private ComboBox _cbElem;

        // 현재 임피던스
        private double _curR=75, _curX=50;
        // 소자 적용 후 임피던스
        private double _newR, _newX;
        private bool   _hasNew;

        public ImpedanceMatchingPanel()
        {
            BackColor=Color.White;
            BuildLayout();
            Recalculate();
        }

        void BuildLayout()
        {
            // ── 좌: 차트 ──
            _chart = new MatchingChartPanel { Dock=DockStyle.Fill };

            var leftPanel = new Panel
            {
                Dock=DockStyle.Left, Width=440, Padding=new Padding(4)
            };
            leftPanel.Controls.Add(_chart);

            // ── 우: 컨트롤 패널 ──
            var right = new Panel
            {
                Dock=DockStyle.Fill, Padding=new Padding(12,8,12,8)
            };

            int y=8;
            Label L(string t,int yy,bool bold=false){
                var l=new Label{Text=t,Location=new Point(0,yy),AutoSize=true,
                    Font=new Font("Malgun Gothic",bold?10.5f:9f,bold?FontStyle.Bold:FontStyle.Regular),
                    ForeColor=bold?Color.FromArgb(20,60,120):Color.FromArgb(50,50,70)};
                right.Controls.Add(l); return l;
            }
            NumericUpDown N(decimal mn,decimal mx,decimal v,int dec,int yy,int w=100){
                var n=new NumericUpDown{Minimum=mn,Maximum=mx,Value=v,DecimalPlaces=dec,
                    Location=new Point(130,yy),Width=w,Font=new Font("Malgun Gothic",9f)};
                right.Controls.Add(n); return n;
            }

            L("임피던스 입력",y,true); y+=24;
            L("R (Ω)",y); _nR=N(0,1e6M,75,2,y); y+=28;
            L("X (Ω)",y); _nX=N(-1e6M,1e6M,50,2,y); y+=28;
            L("Z₀ (Ω)",y); _nZ0=N(1,1000,50,1,y); y+=28;
            L("주파수 (MHz)",y); _nFreq=N(1,100000,1000,1,y); y+=34;

            L("매칭 소자",y,true); y+=24;
            L("소자 타입",y);
            _cbElem=new ComboBox{Location=new Point(130,y),Width=160,
                DropDownStyle=ComboBoxStyle.DropDownList,Font=new Font("Malgun Gothic",9f)};
            _cbElem.Items.AddRange(new[]{"없음","직렬 인덕터 (L)","직렬 커패시터 (C)",
                "병렬 인덕터 (L)","병렬 커패시터 (C)"});
            _cbElem.SelectedIndex=0;
            right.Controls.Add(_cbElem); y+=28;

            L("소자값 (nH/pF)",y); _nVal=N(0.01M,1e6M,10,2,y); y+=34;

            var btnCalc=new Button
            {
                Text="계산 및 스미스차트 표시",
                Location=new Point(0,y), Width=280, Height=32,
                Font=new Font("Malgun Gothic",10f,FontStyle.Bold),
                FlatStyle=FlatStyle.Flat,
                BackColor=Color.FromArgb(24,95,165),
                ForeColor=Color.White, Cursor=Cursors.Hand
            };
            btnCalc.FlatAppearance.BorderSize=0;
            btnCalc.Click+=(s,e)=>Recalculate();
            right.Controls.Add(btnCalc); y+=44;

            L("L-network 자동 설계",y,true); y+=24;
            var btnLnet=new Button
            {
                Text="L-network 매칭 계산 ↗",
                Location=new Point(0,y), Width=200, Height=28,
                Font=new Font("Malgun Gothic",9f),
                FlatStyle=FlatStyle.Flat, Cursor=Cursors.Hand
            };
            btnLnet.Click+=(s,e)=>CalcLNetwork();
            right.Controls.Add(btnLnet); y+=36;

            var btnQwave=new Button
            {
                Text="λ/4 변환기 계산 ↗",
                Location=new Point(0,y), Width=200, Height=28,
                Font=new Font("Malgun Gothic",9f),
                FlatStyle=FlatStyle.Flat, Cursor=Cursors.Hand
            };
            btnQwave.Click+=(s,e)=>CalcQuarterWave();
            right.Controls.Add(btnQwave); y+=36;

            var btnStub=new Button
            {
                Text="단일 스텁 매칭 계산 ↗",
                Location=new Point(0,y), Width=200, Height=28,
                Font=new Font("Malgun Gothic",9f),
                FlatStyle=FlatStyle.Flat, Cursor=Cursors.Hand
            };
            btnStub.Click+=(s,e)=>CalcSingleStub();
            right.Controls.Add(btnStub); y+=44;

            // 결과
            _resultLbl=new Label
            {
                Location=new Point(0,y), Width=310,
                Height=200, Font=new Font("Consolas",8.5f),
                ForeColor=Color.FromArgb(20,60,40),
                BackColor=Color.FromArgb(240,248,242),
                Padding=new Padding(8),
                BorderStyle=BorderStyle.FixedSingle
            };
            right.Controls.Add(_resultLbl);

            // 입력 변경 시 자동 계산
            foreach (var c in new Control[]{_nR,_nX,_nZ0,_nFreq,_cbElem,_nVal})
                if (c is NumericUpDown nd) nd.ValueChanged+=(s,e)=>Recalculate();
                else ((ComboBox)c).SelectedIndexChanged+=(s,e)=>Recalculate();

            Controls.Add(leftPanel);
            Controls.Add(right);
        }

        void Recalculate()
        {
            _curR = (double)_nR.Value;
            _curX = (double)_nX.Value;
            _calc.Z0 = (double)_nZ0.Value;
            double freq = (double)_nFreq.Value;
            double val  = (double)_nVal.Value;

            var gamma  = _calc.ImpedanceToGamma(_curR, _curX);
            double vswr = _calc.CalcVSWR(gamma);
            double rl   = _calc.CalcReturnLoss(gamma);
            double ml   = _calc.CalcMismatchLoss(gamma);

            string xs = _curX >= 0 ? "+" : "";
            string info = $"입력 Z = {_curR:F2}{xs}j{_curX:F2} Ω\n" +
                          $"|Γ| = {gamma.Magnitude:F4}\n" +
                          $"VSWR = {vswr:F3}\n" +
                          $"반사손실 = {rl:F2} dB\n" +
                          $"Mismatch 손실 = {ml:F2} dB\n";

            _hasNew = false;
            int elem = _cbElem?.SelectedIndex ?? 0;
            if (elem > 0)
            {
                (_newR, _newX) = elem switch
                {
                    1 => _calc.ApplySeriesL(_curR, _curX, val, freq),
                    2 => _calc.ApplySeriesC(_curR, _curX, val, freq),
                    3 => _calc.ApplyShuntL(_curR, _curX, val, freq),
                    4 => _calc.ApplyShuntC(_curR, _curX, val, freq),
                    _ => (_curR, _curX)
                };
                _hasNew = true;
                var g2  = _calc.ImpedanceToGamma(_newR, _newX);
                string xs2 = _newX >= 0 ? "+" : "";
                info += $"\n→ 소자 후 Z = {_newR:F2}{xs2}j{_newX:F2} Ω\n" +
                        $"  VSWR = {_calc.CalcVSWR(g2):F3}\n" +
                        $"  RL   = {_calc.CalcReturnLoss(g2):F2} dB";
            }

            _resultLbl.Text = info;
            _chart.SetPoints(_calc, _curR, _curX, _hasNew ? _newR : double.NaN,
                _hasNew ? _newX : double.NaN);
        }

        void CalcLNetwork()
        {
            double src = _calc.Z0, load = _curR;
            if (load <= src) { MessageBox.Show("부하(R)가 Z₀보다 커야 합니다.","알림"); return; }
            double freq = (double)_nFreq.Value;
            var (lS,cSh,cS,lSh) = _calc.LNetworkMatch(src, load, freq);
            _resultLbl.Text =
                $"=== L-network  {src}Ω → {load}Ω @ {freq}MHz ===\n\n" +
                $"[저역통과형]\n  직렬 L = {lS:F3} nH\n  병렬 C = {cSh:F3} pF\n\n" +
                $"[고역통과형]\n  직렬 C = {cS:F3} pF\n  병렬 L = {lSh:F3} nH";
        }

        void CalcQuarterWave()
        {
            double z = _calc.QuarterWaveTransformer(_calc.Z0, _curR);
            _resultLbl.Text =
                $"λ/4 변환기\n\n  Z_transformer = {z:F3} Ω\n\n" +
                $"  (Z₀={_calc.Z0}Ω → R={_curR:F2}Ω)";
        }

        void CalcSingleStub()
        {
            var (stub, line) = _calc.SingleStubMatch(_curR, _curX);
            _resultLbl.Text =
                $"단일 스텁 매칭\n\n" +
                $"  전송선 길이  = {line:F2}°\n" +
                $"  스텁 길이   = {stub:F2}°\n\n" +
                $"  (Z = {_curR:F2}+j{_curX:F2}Ω 기준)";
        }
    }

    // ── 매칭 계산기용 차트 패널 ──
    public class MatchingChartPanel : Control
    {
        private SmithChartCalculator _calc;
        private double _r1,_x1,_r2,_x2;
        private bool   _hasNew;

        public MatchingChartPanel()
        {
            DoubleBuffered=true; ResizeRedraw=true;
            SetStyle(ControlStyles.OptimizedDoubleBuffer|
                     ControlStyles.AllPaintingInWmPaint|ControlStyles.UserPaint,true);
        }

        public void SetPoints(SmithChartCalculator calc,
            double r1,double x1,double r2,double x2)
        {
            _calc=calc; _r1=r1; _x1=x1; _r2=r2; _x2=x2;
            _hasNew=!double.IsNaN(r2);
            Invalidate();
        }

        PointF Sp(double re,double im,float cx,float cy,float rad)
            =>new PointF(cx+(float)(re*rad),cy-(float)(im*rad));

        void ClipDraw(Graphics g,float cx,float cy,float rad,Action act)
        {
            var st=g.Save();
            var gp=new GraphicsPath(); gp.AddEllipse(cx-rad,cy-rad,rad*2,rad*2);
            g.SetClip(gp); act(); g.Restore(st);
        }

        protected override void OnPaint(PaintEventArgs e)
        {
            base.OnPaint(e);
            var g=e.Graphics;
            g.SmoothingMode=SmoothingMode.AntiAlias;
            g.TextRenderingHint=TextRenderingHint.ClearTypeGridFit;
            float cx=Width/2f,cy=Height/2f,rad=Math.Min(cx,cy)-36;

            DrawGrid(g,cx,cy,rad);

            if (_calc==null) return;
            var g1=_calc.ImpedanceToGamma(_r1,_x1);
            var sp1=Sp(g1.Real,g1.Imaginary,cx,cy,rad);

            // VSWR 원 (입력 임피던스 기준)
            float vr=(float)(g1.Magnitude*rad);
            ClipDraw(g,cx,cy,rad,()=>{
                using var vp=new Pen(Color.FromArgb(60,216,90,48),1f){DashStyle=DashStyle.Dash};
                g.DrawEllipse(vp,cx-vr,cy-vr,vr*2,vr*2);
            });

            // 입력 포인트
            g.FillEllipse(Brushes.White,sp1.X-8,sp1.Y-8,16,16);
            g.FillEllipse(new SolidBrush(Color.FromArgb(216,90,48)),sp1.X-7,sp1.Y-7,14,14);
            g.DrawString("ZL",new Font("Arial",8f,FontStyle.Bold),Brushes.Black,sp1.X+9,sp1.Y-8);

            // 소자 후 포인트 및 화살표
            if (_hasNew)
            {
                var g2=_calc.ImpedanceToGamma(_r2,_x2);
                var sp2=Sp(g2.Real,g2.Imaginary,cx,cy,rad);
                using var arr=new Pen(Color.FromArgb(15,110,86),2f);
                arr.CustomEndCap=new AdjustableArrowCap(4,5);
                g.DrawLine(arr,sp1,sp2);
                g.FillEllipse(Brushes.White,sp2.X-8,sp2.Y-8,16,16);
                g.FillEllipse(new SolidBrush(Color.FromArgb(15,110,86)),sp2.X-7,sp2.Y-7,14,14);
                g.DrawString("Z'",new Font("Arial",8f,FontStyle.Bold),Brushes.Black,sp2.X+9,sp2.Y-8);
            }

            // Z₀ 기준점 (원점)
            g.FillEllipse(new SolidBrush(Color.FromArgb(24,95,165)),cx-5,cy-5,10,10);
        }

        void DrawGrid(Graphics g,float cx,float cy,float rad)
        {
            g.FillEllipse(new SolidBrush(Color.FromArgb(245,248,255)),cx-rad,cy-rad,rad*2,rad*2);
            foreach(double mag in new[]{0.25,0.5,0.75})
            {
                float r2=(float)(mag*rad);
                ClipDraw(g,cx,cy,rad,()=>{
                    using var p=new Pen(Color.FromArgb(40,83,74,183),.5f){DashStyle=DashStyle.Dash};
                    g.DrawEllipse(p,cx-r2,cy-r2,r2*2,r2*2);
                });
                double v=(1+mag)/(1-mag);
                g.DrawString(v.ToString("F1"),new Font("Arial",7f),
                    new SolidBrush(Color.FromArgb(90,83,74,183)),cx+r2+2,cy-7);
            }
            foreach(double rn in new[]{0.0,0.5,1.0,2.0})
            {
                float cr=(float)(1.0/(1+rn)*rad),ccx=cx+(float)(rn/(1+rn)*rad);
                bool st=rn==0||rn==1;
                ClipDraw(g,cx,cy,rad,()=>{
                    using var p=new Pen(Color.FromArgb(st?130:50,24,95,165),st?.9f:.5f);
                    g.DrawEllipse(p,ccx-cr,cy-cr,cr*2,cr*2);
                });
            }
            foreach(double xn in new[]{0.5,1.0,2.0})
                foreach(int sign in new[]{1,-1})
                {
                    double xnv=sign*xn;
                    float acx=cx+rad,acy=cy-(float)(1.0/xnv*rad),ar=(float)(Math.Abs(1.0/xnv)*rad);
                    bool st=xn==1.0;
                    ClipDraw(g,cx,cy,rad,()=>{
                        using var p=new Pen(Color.FromArgb(st?115:45,133,79,11),st?.9f:.5f);
                        g.DrawEllipse(p,acx-ar,acy-ar,ar*2,ar*2);
                    });
                }
            g.DrawLine(new Pen(Color.FromArgb(70,80,80,80),.8f),cx-rad,cy,cx+rad,cy);
            g.DrawEllipse(new Pen(Color.FromArgb(140,80,80,80),1.2f),cx-rad,cy-rad,rad*2,rad*2);
            var lf=new Font("Arial",7.5f); var lb=new SolidBrush(Color.FromArgb(120,90,90,90));
            g.DrawString("SC",lf,lb,cx-rad-20,cy-6);
            g.DrawString("OC",lf,lb,cx+rad+3,cy-6);
            g.DrawString("Z₀",lf,lb,cx-8,cy-14);
            g.FillEllipse(lb,cx-2.5f,cy-2.5f,5,5);
        }
    }
}
