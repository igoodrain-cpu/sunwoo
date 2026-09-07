// ════════════════════════════════════════════════════════════════
//  LoadingOverlayForm.cs
//  메인 UI 스레드와 별도의 스레드/메시지 루프에서 실행되는 로딩 창.
//  메인 폼이 차트 렌더링 등으로 오래 블로킹되어도 이 폼의 Marquee
//  애니메이션은 자기 스레드의 메시지 펌프로 계속 돌아간다.
// ════════════════════════════════════════════════════════════════
using System;
using System.Drawing;
using System.Drawing.Drawing2D;
using System.Windows.Forms;

namespace Iruza
{
    public class LoadingOverlayForm : Form
    {
        private const float ScaleFactor = 1.5f;

        private static readonly Color BrandNavy = Color.FromArgb(12, 43, 74);
        private static readonly Color BrandNavyBorder = Color.FromArgb(30, 65, 100);
        private static readonly Color BrandAccent = Color.FromArgb(93, 202, 165);
        private static readonly Color BrandTitleText = Color.FromArgb(245, 247, 250);
        private static readonly Color BrandStatusText = Color.FromArgb(180, 195, 210);

        private Label _statusLabel;
        private ProgressBar _progress;

        public LoadingOverlayForm(Rectangle centerOverScreenBounds, string message)
        {
            FormBorderStyle = FormBorderStyle.None;
            ShowInTaskbar = false;
            TopMost = true;
            StartPosition = FormStartPosition.Manual;
            Size = new Size((int)(280 * ScaleFactor), (int)(140 * ScaleFactor));
            BackColor = BrandNavy;

            Location = new Point(
                centerOverScreenBounds.X + (centerOverScreenBounds.Width - Width) / 2,
                centerOverScreenBounds.Y + (centerOverScreenBounds.Height - Height) / 2);

            Paint += (s, e) =>
            {
                using (var path = RoundedRect(new Rectangle(0, 0, Width - 1, Height - 1), (int)(14 * ScaleFactor)))
                {
                    Region = new Region(path);
                    using (var pen = new Pen(BrandNavyBorder))
                        e.Graphics.DrawPath(pen, path);
                }
            };

            var titleLabel = new Label
            {
                Text = "RF Impedance Analyzer",
                Font = new Font("Malgun Gothic", 10.5f * ScaleFactor, FontStyle.Bold),
                ForeColor = BrandTitleText,
                AutoSize = false,
                Size = new Size((int)(240 * ScaleFactor), (int)(24 * ScaleFactor)),
                Location = new Point((int)(20 * ScaleFactor), (int)(22 * ScaleFactor)),
                TextAlign = ContentAlignment.MiddleCenter
            };

            _progress = new ProgressBar
            {
                Style = ProgressBarStyle.Marquee,
                MarqueeAnimationSpeed = 30,
                Size = new Size((int)(200 * ScaleFactor), (int)(4 * ScaleFactor)),
                Location = new Point((int)(40 * ScaleFactor), (int)(68 * ScaleFactor)),
                ForeColor = BrandAccent
            };

            _statusLabel = new Label
            {
                Text = message,
                Font = new Font("Malgun Gothic", 9f * ScaleFactor),
                ForeColor = BrandStatusText,
                AutoSize = false,
                Size = new Size((int)(240 * ScaleFactor), (int)(20 * ScaleFactor)),
                Location = new Point((int)(20 * ScaleFactor), (int)(94 * ScaleFactor)),
                TextAlign = ContentAlignment.MiddleCenter
            };

            Controls.Add(titleLabel);
            Controls.Add(_progress);
            Controls.Add(_statusLabel);
        }

        // 로딩 폼은 별도 스레드에서 돌아가므로, 메시지를 바꿀 때는
        // 반드시 이 폼 자신의 스레드로 Invoke해서 호출해야 한다.
        public void UpdateMessage(string message)
        {
            if (IsDisposed) return;

            if (InvokeRequired)
            {
                try { Invoke(new Action(() => UpdateMessage(message))); }
                catch (ObjectDisposedException) { }
                catch (InvalidOperationException) { }
                return;
            }

            _statusLabel.Text = message;
        }

        private static GraphicsPath RoundedRect(Rectangle bounds, int radius)
        {
            int d = radius * 2;
            var path = new GraphicsPath();
            path.AddArc(bounds.X, bounds.Y, d, d, 180, 90);
            path.AddArc(bounds.Right - d, bounds.Y, d, d, 270, 90);
            path.AddArc(bounds.Right - d, bounds.Bottom - d, d, d, 0, 90);
            path.AddArc(bounds.X, bounds.Bottom - d, d, d, 90, 90);
            path.CloseFigure();
            return path;
        }
    }
}
