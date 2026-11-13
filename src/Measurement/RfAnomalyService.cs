// ════════════════════════════════════════════════════════════════
//  RfAnomalyService.cs  –  AI 이상 진단 연동 계층 (2년차 WP4)
//  Robust Mahalanobis(MCD) + Isolation Forest + 궤적 잔차 앙상블(AnomalyEnsemble.cs)을
//  Iruza 데이터(MeasurementStep)에 연결합니다.
//   - 특성 정의 : MeasurementStep → double[]  (학습·진단이 반드시 같은 정의를 쓰도록 한 곳에서 관리)
//   - 학습      : 체크한 Golden Run → 채널별 Recipe·Step 모델 → Models\rf_anomaly_model.json.gz
//   - 진단      : 데이터셋의 스텝마다 AnomalyResult (ds.Steps와 같은 순서, 판정 불가 스텝은 null)
//  ※ WinForms에 의존하지 않으므로 Worker Service 등 다른 프로그램에서도 그대로 사용 가능
//  만든이: 이선우
// ════════════════════════════════════════════════════════════════
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Iruza.Diagnostics.Anomaly;

namespace Iruza
{
    // Golden Run 학습용 – Run 하나의 채널별 측정 데이터 (MeasurementDb.GetMeasurementDatasetsByRunNames 결과)
    internal sealed class RunMeasurementDataset
    {
        public long RunId { get; set; }
        public string RunName { get; set; }
        public string RecipeName { get; set; }
        public MeasurementDataset Dataset { get; set; }
    }

    // AI 진단에 쓰는 특성 정의입니다. 항목을 바꾸면 기존 모델은 불러오지 않으므로 다시 학습해야 합니다.
    internal static class RfFeatures
    {
        // (표시 이름, 추출 함수) — 이름은 화면의 '기여 변수'에 그대로 표시됩니다.
        // 제외한 항목과 이유:
        //  · Ref(반사전력)·|Γ|·VSWR·RL : R·X(·Fwd)로 결정되는 중복 정보이면서, 정합점 근처에서 임피던스 변화에
        //                              V자(2차)로 반응하는 비선형 값이라 MD의 정상 꼬리를 크게 부풀림
        //  · Del(전달전력)             : ≈ Fwd − Ref 중복
        //  · Vdc                      : Output sensor에서만 의미 있음
        private static readonly (string Name, Func<MeasurementStep, double> Get)[] Defs =
        {
            ("R",       s => s.R),
            ("X",       s => s.X),
            ("θ",       s => s.Phase_deg),
            ("Vout",    s => s.Vout_Vrms),
            ("Iout",    s => s.Iout_Arms),
            ("Fwd",     s => s.ForwardP_W),
            ("VVC1",    s => s.VVC1),
            ("VVC2",    s => s.VVC2),
            ("VVC3",    s => s.VVC3),
            ("APC Pre", s => s.APC_Pressure),
            ("APC Pos", s => s.APC_Position),
            ("Ar",      s => s.Ar_Flow),
            ("O2",      s => s.O2_Flow),
        };

        public static readonly string[] Names = Defs.Select(d => d.Name).ToArray();

        public static int IndexOf(string name) => Array.IndexOf(Names, name);

        /// <summary>측정 불가 스텝(|Γ| > 1.05, NaN/∞)이면 false</summary>
        public static bool TryExtract(MeasurementStep s, out double[] features)
        {
            features = null;
            if (s == null || !(s.GammaMag <= 1.05)) return false;

            var v = new double[Defs.Length];
            for (int i = 0; i < Defs.Length; i++)
            {
                double x = Defs[i].Get(s);
                if (double.IsNaN(x) || double.IsInfinity(x)) return false;
                v[i] = x;
            }
            features = v;
            return true;
        }
    }

    // 채널 하나(source / bias / source_out / bias_out)의 학습 모델
    public sealed class RfChannelModel
    {
        public string Channel { get; set; }
        public DateTime TrainedAt { get; set; }
        public List<string> GoldenRuns { get; set; } = new List<string>();
        public int TrainSamples { get; set; }
        public int CalibSamples { get; set; }
        public double TargetFpr { get; set; }
        public StepAwareDetector Detector { get; set; }
    }

    // 모델 파일 전체 (채널별 모델 묶음)
    public sealed class RfAnomalyModelSet
    {
        public int FormatVersion { get; set; } = 1;
        public string[] FeatureNames { get; set; }
        public Dictionary<string, RfChannelModel> Channels { get; set; } = new Dictionary<string, RfChannelModel>();
    }

    internal sealed class RfAnomalyService
    {
        // ── 학습 설정 (현장 Golden Run 확보량에 맞춰 조정) ──────────────
        /// <summary>Golden 기준 목표 오탐률(스텝 단위). Golden Run이 수백 개 이상 쌓이면 0.01로 낮추세요.</summary>
        public const double TargetFpr = 0.02;
        /// <summary>교차 보정 fold 수 — 각 Run이 한 번씩 '학습에 안 쓰인 보정 표본'이 됩니다 (Run 단위 분할)</summary>
        public const int CrossFitFolds = 5;
        /// <summary>학습에 필요한 최소 Golden Run 수</summary>
        public const int MinGoldenRuns = 20;
        /// <summary>Recipe·Step 모델 최소 학습 표본 = 이 값 × 특성 수(13). 부족한 Step은 GLOBAL 모델로 대체</summary>
        public const int MinSamplesPerFeature = 4;
        /// <summary>Recipe·Step 모델 최소 표본(= 보정 표본) 수</summary>
        public const int MinCalibSamples = 30;

        public static string DefaultModelPath =>
            Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "Models", "rf_anomaly_model.json.gz");

        // 학습이 끝나면 새 객체로 통째로 교체 → 진단 중인 다른 스레드와 충돌하지 않음
        private volatile RfAnomalyModelSet _model;

        public RfAnomalyModelSet Model => _model;
        public bool IsLoaded => _model != null && _model.Channels.Count > 0;
        public bool HasChannel(string channel) => _model != null && _model.Channels.ContainsKey(channel);
        public string ModelPath { get; private set; }

        // 궤적 잔차 보조 검출기 — 정상 궤적 '주변'의 비선형 이탈을 잡습니다.
        // 현장 데이터에서 관계가 뚜렷한 쌍을 찾으면 여기에 추가하세요 (예: VVC2 vs APC Pre).
        private static EnsembleOptions BuildOptions()
        {
            var opt = new EnsembleOptions { TargetFpr = TargetFpr, Mode = FusionMode.CalibratedMax };
            opt.TrajectoryResiduals.Add(new ResidualSpec
            {
                Name = "X|R",
                Target = RfFeatures.IndexOf("X"),
                Reference = RfFeatures.IndexOf("R"),
                Degree = 2
            });
            return opt;
        }

        // ── 학습 ────────────────────────────────────────────────
        /// <summary>
        /// 체크한 Golden Run으로 지정 채널들의 모델을 학습합니다. 다른 채널의 기존 모델은 유지됩니다.
        /// (DB 조회 포함, 백그라운드 스레드에서 호출)
        /// </summary>
        /// <param name="loadRuns">Run 데이터 로더. null이면 MeasurementDb.GetMeasurementDatasetsByRunNames</param>
        /// <returns>학습 결과 요약 (화면 표시용)</returns>
        public string Train(IList<string> goldenRunNames, IEnumerable<string> channels,
                            Func<IList<string>, string, List<RunMeasurementDataset>> loadRuns = null)
        {
            var names = goldenRunNames.Where(n => !string.IsNullOrWhiteSpace(n)).Distinct().ToList();
            if (names.Count < MinGoldenRuns)
                throw new InvalidOperationException($"Golden Run이 {names.Count}개입니다. 최소 {MinGoldenRuns}개 이상 체크해 주세요.");

            if (loadRuns == null) loadRuns = (runNames, ch) => MeasurementDb.GetMeasurementDatasetsByRunNames(runNames, ch);

            // 기존 모델의 다른 채널은 그대로 가져감 (특성 정의가 같을 때만)
            var old = _model;
            var set = new RfAnomalyModelSet { FeatureNames = RfFeatures.Names };
            if (old != null && old.FeatureNames != null && old.FeatureNames.SequenceEqual(RfFeatures.Names))
                foreach (var kv in old.Channels) set.Channels[kv.Key] = kv.Value;

            int p = RfFeatures.Names.Length;
            var report = new List<string>();

            foreach (var ch in channels)
            {
                var runs = loadRuns(names, ch);
                var samples = new List<RfSample>();
                int alarmSkipped = 0, invalidSkipped = 0;

                foreach (var run in runs)
                {
                    if (run?.Dataset?.Steps == null) continue;
                    foreach (var st in run.Dataset.Steps)
                    {
                        // 알람 스텝은 정상 기준에서 제외
                        if (st.Proc_Status == "Heavy alarm") { alarmSkipped++; continue; }
                        if (!RfFeatures.TryExtract(st, out double[] f)) { invalidSkipped++; continue; }

                        // Tag = Run 이름 → 교차 보정 시 같은 Run의 스텝은 같은 fold로 묶임
                        samples.Add(new RfSample { Recipe = run.RecipeName ?? "", Step = st.Step, Features = f, Tag = run.RunName });
                    }
                }

                if (samples.Count < 4 * (p + 1) || runs.Count < CrossFitFolds * 2)
                {
                    report.Add($"[{ch}] 학습 안 함 — 유효 스텝 부족 (스텝 {samples.Count}, DB에서 찾은 Run {runs.Count}개)");
                    continue;
                }

                var det = StepAwareDetector.FitCrossFitted(samples, RfFeatures.Names, BuildOptions(), CrossFitFolds,
                                                           MinSamplesPerFeature, MinCalibSamples);

                set.Channels[ch] = new RfChannelModel
                {
                    Channel = ch,
                    TrainedAt = DateTime.Now,
                    GoldenRuns = runs.Select(r => r.RunName).Distinct().OrderBy(n => n).ToList(),
                    TrainSamples = samples.Count,
                    CalibSamples = samples.Count,   // 교차 보정: 모든 스텝이 out-of-fold 보정 표본
                    TargetFpr = TargetFpr,
                    Detector = det
                };

                var keys = samples.Select(s => StepAwareDetector.KeyOf(s.Recipe, s.Step)).Distinct().OrderBy(k => k).ToList();
                var fallback = keys.Where(k => !det.Models.ContainsKey(k)).ToList();

                report.Add($"[{ch}] Golden {runs.Count} Run · 스텝 {samples.Count} ({CrossFitFolds}-fold 교차 보정)" +
                           (alarmSkipped + invalidSkipped > 0 ? $" · 제외 {alarmSkipped + invalidSkipped} (알람 {alarmSkipped}, 측정불가 {invalidSkipped})" : ""));
                report.Add($"    Recipe·Step 모델 {det.Models.Count}개" +
                           (det.Models.Count > 0 ? ": " + Abbreviate(det.Models.Keys.OrderBy(k => k)) : ""));
                if (fallback.Count > 0)
                    report.Add($"    표본 부족 → GLOBAL(참고용) 적용 {fallback.Count}개: {Abbreviate(fallback)}");
            }

            if (set.Channels.Count == 0 || !channels.Any(set.Channels.ContainsKey))
                throw new InvalidOperationException("학습된 채널이 없습니다.\n\n" + string.Join(Environment.NewLine, report));

            _model = set;
            return string.Join(Environment.NewLine, report);
        }

        private static string Abbreviate(IEnumerable<string> items, int max = 8)
        {
            var list = items.ToList();
            return list.Count <= max ? string.Join(", ", list) : string.Join(", ", list.Take(max)) + $" 외 {list.Count - max}개";
        }

        // ── 진단 ────────────────────────────────────────────────
        /// <summary>
        /// 데이터셋의 각 스텝을 진단합니다. 반환 목록은 ds.Steps와 같은 순서이며, 판정할 수 없는 스텝은 null입니다.
        /// 해당 채널 모델이 없으면 null을 반환합니다. (스레드 안전)
        /// </summary>
        public List<AnomalyResult> Diagnose(string recipeName, string channel, MeasurementDataset ds)
        {
            var m = _model;
            if (m == null || ds?.Steps == null || channel == null) return null;
            if (!m.Channels.TryGetValue(channel, out RfChannelModel cm) || cm?.Detector == null) return null;

            var result = new List<AnomalyResult>(ds.Steps.Count);
            foreach (var st in ds.Steps)
            {
                if (!RfFeatures.TryExtract(st, out double[] f)) { result.Add(null); continue; }
                result.Add(cm.Detector.Diagnose(new RfSample { Recipe = recipeName ?? "", Step = st.Step, Features = f }));
            }
            return result;
        }

        // ── 저장 / 불러오기 ──────────────────────────────────────
        public bool TryLoad(string path, out string error)
        {
            error = null;
            if (!File.Exists(path)) { error = "모델 파일이 없습니다.\n" + path; return false; }
            try
            {
                var m = GzipJson.Read<RfAnomalyModelSet>(path);

                if (m?.Channels == null || m.Channels.Count == 0)
                {
                    error = "모델 파일에 학습된 채널이 없습니다.";
                    return false;
                }
                if (m.FeatureNames == null || !m.FeatureNames.SequenceEqual(RfFeatures.Names))
                {
                    error = "모델의 특성 정의가 현재 프로그램과 다릅니다.\nAI 진단 → Golden Run 학습으로 다시 학습해 주세요.";
                    return false;
                }
                _model = m;
                ModelPath = path;
                return true;
            }
            catch (Exception ex)
            {
                error = ex.Message;
                return false;
            }
        }

        /// <summary>현재 모델을 저장합니다. 임시 파일에 쓴 뒤 교체하므로 저장 중 오류가 나도 기존 파일은 보존됩니다.</summary>
        public void Save(string path)
        {
            var m = _model ?? throw new InvalidOperationException("저장할 모델이 없습니다.");
            Directory.CreateDirectory(Path.GetDirectoryName(path));
            string tmp = path + ".tmp";
            GzipJson.Write(tmp, m);
            File.Copy(tmp, path, true);
            File.Delete(tmp);
            ModelPath = path;
        }

        // ── 표시용 ─────────────────────────────────────────────
        /// <summary>좌측 상태 표시용 한 줄 요약</summary>
        public string ShortDescribe(string channel)
        {
            var m = _model;
            if (m == null || !m.Channels.TryGetValue(channel, out RfChannelModel cm)) return "";
            return $"{cm.TrainedAt:yyyy-MM-dd} · Golden {cm.GoldenRuns.Count} Run";
        }

        /// <summary>모델 정보 창 내용</summary>
        public string Describe()
        {
            var m = _model;
            if (m == null || m.Channels.Count == 0) return "불러온 AI 모델이 없습니다.";

            var lines = new List<string>
            {
                "Robust Mahalanobis(MCD) + Isolation Forest + 궤적 잔차 앙상블",
                "파일: " + (ModelPath ?? "(저장 안 됨)"),
                "특성: " + string.Join(", ", m.FeatureNames),
                ""
            };
            foreach (var cm in m.Channels.Values.OrderBy(c => c.Channel))
            {
                var det = cm.Detector;
                lines.Add($"[{cm.Channel}]  학습 {cm.TrainedAt:yyyy-MM-dd HH:mm}  ·  목표 오탐률 {cm.TargetFpr:P0}");
                lines.Add($"    Golden {cm.GoldenRuns.Count} Run  ·  스텝 {cm.TrainSamples} ({CrossFitFolds}-fold 교차 보정)");
                lines.Add($"    Recipe·Step 모델 {det?.Models.Count ?? 0}개" +
                          (det != null && det.Models.Count > 0 ? ": " + Abbreviate(det.Models.Keys.OrderBy(k => k)) : ""));
            }
            return string.Join(Environment.NewLine, lines);
        }
    }
}
