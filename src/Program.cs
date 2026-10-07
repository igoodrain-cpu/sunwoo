// ════════════════════════════════════════════════════════════════
//  Iruza – RF Smith Chart Analyzer
//  H&iruja Inc.  |  Plasma 장비 RF 임피던스 매칭 분석 솔루션
//  만든이: 이선우
// ════════════════════════════════════════════════════════════════
using System;
using System.Windows.Forms;

namespace Iruza
{
    // WinForms 시각 스타일을 설정하고 메인 셸을 시작합니다.
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
