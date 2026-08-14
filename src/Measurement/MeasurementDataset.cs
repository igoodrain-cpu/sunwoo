// ════════════════════════════════════════════════════════════════
//  MeasurementDataset.cs  –  측정 데이터셋 (CSV 입출력 포함)
// ════════════════════════════════════════════════════════════════
using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Text;

namespace Iruza
{
    public class MeasurementDataset
    {
        public string Name  { get; set; } = "측정 데이터";
        public double Z0    { get; set; } = 50.0;
        public List<MeasurementStep> Steps { get; } = new List<MeasurementStep>();

        // ── 통계 ──
        public MeasurementStep BestVSWR
            => Steps.Where(s => s.VSWR < 99).OrderBy(s => s.VSWR).FirstOrDefault();
        public MeasurementStep WorstVSWR
            => Steps.Where(s => s.VSWR < 99).OrderByDescending(s => s.VSWR).FirstOrDefault();
        public double AvgVSWR
            => Steps.Any(s => s.VSWR < 99) ? Steps.Where(s => s.VSWR < 99).Average(s => s.VSWR) : 0;
        public double AvgEfficiency
            => Steps.Count == 0 ? 0 : Steps.Average(s => s.Efficiency_pct);

        // ── 빌더 헬퍼 (수동 추가) ──
        public MeasurementDataset Add(int step, double vout, double iout, double phase,
            double fwdP = 0)
        {
            var ms = new MeasurementStep
                { Step=step, Vout_Vrms=vout, Iout_Arms=iout, Phase_deg=phase, ForwardP_W=fwdP };
            ms.ComputeFromVI(Z0);
            Steps.Add(ms);
            return this;
        }

        public MeasurementDataset AddZ(int step, double r, double x,
            double vout=0, double iout=0, double phase=0, double fwdP=0)
        {
            var ms = new MeasurementStep
                { Step=step, R=r, X=x, Vout_Vrms=vout, Iout_Arms=iout, Phase_deg=phase, ForwardP_W=fwdP };
            if (vout > 0 && iout > 0) ms.ComputeFromVI(Z0);
            else ms.ComputeFromZ(Z0);
            Steps.Add(ms);
            return this;
        }

        // ── CSV 가져오기 ──
        public static MeasurementDataset FromCsv(string path, double z0 = 50.0)
        {
            var ds = new MeasurementDataset { Z0 = z0, Name = Path.GetFileNameWithoutExtension(path) };
            var lines = File.ReadAllLines(path, Encoding.UTF8);
            for (int i = 1; i < lines.Length; i++)
            {
                var line = lines[i].Trim();
                if (string.IsNullOrEmpty(line) || line.StartsWith("#")) continue;
                var ms = ParseLine(line, z0);
                if (ms != null) ds.Steps.Add(ms);
            }
            return ds;
        }

        static double D(string[] cols, int i)
        {
            if (i >= cols.Length) return 0;
            return double.TryParse(cols[i].Trim().Trim('"'), NumberStyles.Any,
                CultureInfo.InvariantCulture, out var v) ? v : 0;
        }

        static MeasurementStep ParseLine(string line, double z0)
        {
            var cols = line.Split(',');
            if (cols.Length < 3) return null;
            var ms = new MeasurementStep
            {
                Step         = (int)D(cols, 0),
                Vout_Vrms    = D(cols, 1),
                Iout_Arms    = D(cols, 2),
                Phase_deg    = D(cols, 3),
                R            = D(cols, 4),
                X            = D(cols, 5),
                Gamma_Real   = D(cols, 6),
                Gamma_Imag   = D(cols, 7),
                VSWR         = D(cols, 9),
                Z_Text       = cols.Length > 10 ? cols[10].Trim().Trim('"') : "",
                Z_Normalized = cols.Length > 11 ? cols[11].Trim().Trim('"') : "",
                ForwardP_W   = D(cols, 12),
                ReflectedP_W = D(cols, 13),
                DeliveredP_W = D(cols, 14),
            };
            if (ms.Gamma_Real == 0 && ms.Gamma_Imag == 0)
                ms.ComputeFromZ(z0);
            else if (ms.VSWR == 0)
            {
                double mag = ms.GammaMag;
                ms.VSWR = mag >= 1 ? 99.9 : (1 + mag) / (1 - mag);
            }
            return ms;
        }

        // ── CSV 내보내기 ──
        public void ToCsv(string path)
        {
            var sb = new StringBuilder();
            sb.AppendLine("Step,Vout (Vrms),Iout (Arms),Phase θ (deg),R (Ω),X (Ω)," +
                          "Γ real,Γ imag,|Γ|,VSWR,Z text,z normalized," +
                          "Forward P (W),Reflected P (W),Delivered P (W)");
            var ci = CultureInfo.InvariantCulture;
            foreach (var s in Steps)
                sb.AppendLine(string.Join(",",
                    s.Step,
                    s.Vout_Vrms.ToString("F4",ci), s.Iout_Arms.ToString("F4",ci),
                    s.Phase_deg.ToString("F2",ci),
                    s.R.ToString("F4",ci), s.X.ToString("F4",ci),
                    s.Gamma_Real.ToString("F6",ci), s.Gamma_Imag.ToString("F6",ci),
                    s.GammaMag.ToString("F6",ci), s.VSWR.ToString("F4",ci),
                    $"\"{s.Z_Text}\"", $"\"{s.Z_Normalized}\"",
                    s.ForwardP_W.ToString("F4",ci), s.ReflectedP_W.ToString("F4",ci),
                    s.DeliveredP_W.ToString("F4",ci)));
            File.WriteAllText(path, sb.ToString(), Encoding.UTF8);
        }

        // ── 샘플 데이터 생성 ──
        public static MeasurementDataset CreateSample(string pName)
        {
            var ds = new MeasurementDataset { Name = pName, Z0 = 50 };
            ds.Add(1,  10.0, 0.200,  0.0,  100)
              .Add(2,  10.0, 0.185, 15.0,   90)
              .Add(3,  10.0, 0.168, 30.0,   80)
              .Add(4,  10.0, 0.141, 45.0,   70)
              .Add(5,  10.0, 0.120, 20.0,   60)
              .AddZ(6,  75,  50, 10, 0.109, 33.7)
              .AddZ(7,  50,  30, 10, 0.155, 19.3)
              .AddZ(8,  30, -20, 10, 0.241,-32.0)
              .AddZ(9,  25,   0, 10, 0.277,  0.0)
              .AddZ(10, 50,   0, 10, 0.200,  0.0, 100);
            ds.Steps[0].ForwardP_W   = 100;
            ds.Steps[0].ReflectedP_W = 4;
            ds.Steps[0].DeliveredP_W = 96;
            return ds;
        }
        public static MeasurementDataset CreateSampleBt(string pName)
        {
            var ds = new MeasurementDataset { Name = pName, Z0 = 50 };
            ds.Add(1, 10.0, 0.100, 0.0, 100)
              .Add(2, 10.0, 0.155, 15.0, 90)
              .Add(3, 10.0, 0.138, 30.0, 80)
              .Add(4, 10.0, 0.151, 45.0, 70)
              .Add(5, 10.0, 0.120, 20.0, 60)
              .AddZ(6, 75, 50, 30, 0.109, 33.7)
              .AddZ(7, 50, 30, 10, 0.155, 19.3)
              .AddZ(8, 30, -20, 10, 0.241, -32.0)
              .AddZ(9, 25, 0, 10, 0.277, 0.0)
              .AddZ(10, 50, 0, 10, 0.200, 0.0, 100);
            ds.Steps[0].ForwardP_W = 100;
            ds.Steps[0].ReflectedP_W = 4;
            ds.Steps[0].DeliveredP_W = 96;
            return ds;
        }
    }
}
