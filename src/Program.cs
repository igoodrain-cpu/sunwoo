// ════════════════════════════════════════════════════════════════
//  Iruza – RF Smith Chart Analyzer
//  H&iruja Inc.  |  Plasma 장비 RF 임피던스 매칭 분석 솔루션
// ════════════════════════════════════════════════════════════════
using System;
using System.Windows.Forms;

namespace Iruza
{
    static class Program
    {
        [STAThread]
        static void Main()
        {
            Application.EnableVisualStyles();
            Application.SetCompatibleTextRenderingDefault(false);
            Application.Run(new MainShell());
        }
    }
}
