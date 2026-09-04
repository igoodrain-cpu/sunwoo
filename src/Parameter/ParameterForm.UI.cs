using System;
using System.ComponentModel;
using System.Drawing;
using System.Drawing.Drawing2D;
//using System.Drawing.Drawing2D;
using System.Linq;
using System.Runtime.InteropServices;
using System.Windows.Forms;

namespace Iruza.src.Parameter
{
    public partial class ParameterForm
    {
        private const int WmNclButtonDown = 0xA1;
        private const int HtCaption = 0x2;
        private RoundedPanel _borderHost;
        private Panel _contentHost;

        [DllImport("user32.dll")]
        private static extern bool ReleaseCapture();

        [DllImport("user32.dll")]
        private static extern IntPtr SendMessage(IntPtr hWnd, int msg, int wParam, int lParam);

        private void InitializeChrome()
        {
            if (IsInDesignMode() || _borderHost != null)
            {
                return;
            }

            SuspendLayout();

            var existingControls = Controls.Cast<Control>().ToArray();

            _borderHost = new RoundedPanel
            {
                Dock = DockStyle.Fill,
                Margin = Padding.Empty,
                Padding = new Padding(5),
                BackColor = Color.White,
                BorderColor = Color.Gray,
                BorderThickness = 1,
                CornerRadius = 18
            };

            _contentHost = new Panel
            {
                Dock = DockStyle.Fill,
                Margin = Padding.Empty,
                Padding = Padding.Empty,
                BackColor = Color.White
            };

            _borderHost.Controls.Add(_contentHost);

            foreach (Control control in existingControls)
            {
                Controls.Remove(control);
            }

            Controls.Add(_borderHost);

            foreach (Control control in existingControls)
            {
                _contentHost.Controls.Add(control);
            }

            ApplyBorderHostRegion();

            ResumeLayout(true);
        }

        protected override void OnShown(EventArgs e)
        {
            base.OnShown(e);
            ApplyRoundedRegion();
            ApplyBorderHostRegion();
        }

        protected override void OnResize(EventArgs e)
        {
            base.OnResize(e);
            ApplyRoundedRegion();
            ApplyBorderHostRegion();
            Invalidate();
        }

        protected override void OnPaint(PaintEventArgs e)
        {
            base.OnPaint(e);
        }

        private void ApplyRoundedRegion()
        {
            if (IsInDesignMode())
            {
                return;
            }

            if (ClientSize.Width <= 0 || ClientSize.Height <= 0)
            {
                return;
            }

            using (var path = UiShapeFactory.CreateRoundedRectangle(new Rectangle(0, 0, ClientSize.Width - 1, ClientSize.Height - 1), 18))
            {
                Region = new Region(path);
            }
        }

        private void ApplyBorderHostRegion()
        {
            if (IsInDesignMode() || _borderHost == null)
            {
                return;
            }

            if (_borderHost.Width <= 0 || _borderHost.Height <= 0)
            {
                return;
            }

            using (var path = UiShapeFactory.CreateRoundedRectangle(new Rectangle(0, 0, _borderHost.Width - 1, _borderHost.Height - 1), _borderHost.CornerRadius))
            {
                _borderHost.Region = new Region(path);
            }
        }

        private void btnClose_Click(object sender, EventArgs e)
        {
            Close();
        }

        private void pnlHeader_MouseDown(object sender, MouseEventArgs e)
        {
            if (e.Button != MouseButtons.Left)
            {
                return;
            }

            ReleaseCapture();
            SendMessage(Handle, WmNclButtonDown, HtCaption, 0);
        }

        private bool IsInDesignMode()
        {
            return LicenseManager.UsageMode == LicenseUsageMode.Designtime ||
                   DesignMode ||
                   (Site?.DesignMode ?? false);
        }
    }

    internal static class UiShapeFactory
    {
        public static GraphicsPath CreateRoundedRectangle(Rectangle bounds, int radius)
        {
            var path = new GraphicsPath();
            var diameter = Math.Max(1, radius * 2);
            var arc = new Rectangle(bounds.Location, new Size(diameter, diameter));

            path.StartFigure();
            path.AddArc(arc, 180, 90);
            arc.X = bounds.Right - diameter;
            path.AddArc(arc, 270, 90);
            arc.Y = bounds.Bottom - diameter;
            path.AddArc(arc, 0, 90);
            arc.X = bounds.Left;
            path.AddArc(arc, 90, 90);
            path.CloseFigure();

            return path;
        }
    }

    [DesignerCategory("Code")]
    public class RoundedPanel : Panel
    {
        private int _cornerRadius = 16;
        private int _borderThickness = 1;
        private Color _borderColor = Color.FromArgb(221, 227, 238);

        public RoundedPanel()
        {
            SetStyle(ControlStyles.UserPaint |
                     ControlStyles.AllPaintingInWmPaint |
                     ControlStyles.OptimizedDoubleBuffer |
                     ControlStyles.ResizeRedraw, true);
            DoubleBuffered = true;
            ResizeRedraw = true;
            BackColor = Color.White;
        }

        public int CornerRadius
        {
            get => _cornerRadius;
            set
            {
                _cornerRadius = Math.Max(1, value);
                Invalidate();
            }
        }

        public int BorderThickness
        {
            get => _borderThickness;
            set
            {
                _borderThickness = Math.Max(1, value);
                Invalidate();
            }
        }

        public Color BorderColor
        {
            get => _borderColor;
            set
            {
                _borderColor = value;
                Invalidate();
            }
        }

        protected override void OnPaint(PaintEventArgs e)
        {
            if (Width <= 0 || Height <= 0)
            {
                base.OnPaint(e);
                return;
            }

            base.OnPaint(e);

            e.Graphics.SmoothingMode = SmoothingMode.AntiAlias;
            e.Graphics.PixelOffsetMode = PixelOffsetMode.HighQuality;

            var inset = Math.Max(1, BorderThickness);
            var rect = new Rectangle(inset, inset, Width - (inset * 2) - 1, Height - (inset * 2) - 1);
            var radius = Math.Max(1, CornerRadius - inset);

            if (rect.Width <= 0 || rect.Height <= 0)
            {
                return;
            }

            using (var path = UiShapeFactory.CreateRoundedRectangle(rect, radius))
            using (var brush = new SolidBrush(BackColor))
            using (var pen = new Pen(BorderColor, BorderThickness))
            {
                e.Graphics.FillPath(brush, path);
                e.Graphics.DrawPath(pen, path);
            }
        }
    }

    [DesignerCategory("Code")]
    public class RoundedButton : Button
    {
        private int _cornerRadius = 12;
        private int _borderThickness = 1;
        private Color _borderColor = Color.FromArgb(214, 223, 238);
        private Color _fillColor = Color.White;
        private Color _textColor = Color.FromArgb(31, 41, 55);

        public RoundedButton()
        {
            FlatStyle = FlatStyle.Flat;
            FlatAppearance.BorderSize = 0;
            DoubleBuffered = true;
            ResizeRedraw = true;
            Cursor = Cursors.Hand;
        }

        public int CornerRadius
        {
            get => _cornerRadius;
            set
            {
                _cornerRadius = Math.Max(1, value);
                Invalidate();
            }
        }

        public int BorderThickness
        {
            get => _borderThickness;
            set
            {
                _borderThickness = Math.Max(1, value);
                Invalidate();
            }
        }

        public Color BorderColor
        {
            get => _borderColor;
            set
            {
                _borderColor = value;
                Invalidate();
            }
        }

        public Color FillColor
        {
            get => _fillColor;
            set
            {
                _fillColor = value;
                Invalidate();
            }
        }

        public Color TextColor
        {
            get => _textColor;
            set
            {
                _textColor = value;
                ForeColor = value;
                Invalidate();
            }
        }

        protected override void OnPaint(PaintEventArgs pevent)
        {
            if (Width <= 0 || Height <= 0 || Font == null)
            {
                base.OnPaint(pevent);
                return;
            }

            pevent.Graphics.SmoothingMode = SmoothingMode.AntiAlias;

            var rect = new Rectangle(0, 0, Width - 1, Height - 1);
            using (var path = UiShapeFactory.CreateRoundedRectangle(rect, CornerRadius))
            using (var brush = new SolidBrush(Enabled ? FillColor : Color.FromArgb(234, 238, 244)))
            using (var pen = new Pen(BorderColor, BorderThickness))
            using (var textBrush = new SolidBrush(Enabled ? TextColor : Color.FromArgb(153, 161, 175)))
            using (var sf = new StringFormat { Alignment = StringAlignment.Center, LineAlignment = StringAlignment.Center })
            {
                pevent.Graphics.FillPath(brush, path);
                pevent.Graphics.DrawPath(pen, path);
                pevent.Graphics.DrawString(Text, Font, textBrush, rect, sf);
            }
        }
    }
}
