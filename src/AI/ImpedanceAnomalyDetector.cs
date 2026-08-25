// ImpedanceAnomalyDetector.cs
// -----------------------------------------------------------------------------
// Iruza (C# WinForms) 통합용 - 스미스 차트 임피던스 궤적 이상탐지 (정상/비정상)
//
// Python 프로토타입(impedance_anomaly_detection.py)의 Method A / Method D를
// 외부 라이브러리 없이 순수 수학 연산으로 포팅한 버전.
//   - Method A: 스텝 간 Γ(반사계수) 이동거리의 Z-score  → 급격한 튐(jump) 탐지
//   - Method D: CUSUM (누적합) 변화점 탐지               → 궤적 중간의 레벨 변화 탐지
//
// System.Numerics.Complex 는 .NET BCL 내장이라 NuGet 설치가 필요 없습니다.
// Isolation Forest(Method C), Mahalanobis(Method B)는 데이터가 더 쌓인 뒤
// ONNX Runtime 또는 ML.NET으로 별도 추가하는 것을 권장합니다 (README 하단 참고).
// -----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

namespace Iruza
{
    /// <summary>
    /// 매처(matcher)에서 수신한 1개 스텝의 측정 데이터.
    /// CSV 컬럼(Vout_Vrms, Iout_Arms, R, X, VSWR ...)과 1:1 매핑됩니다.
    /// </summary>
    public class ImpedanceStepData
    {
        public int Step { get; set; }
        public double R { get; set; }        // Ω
        public double X { get; set; }        // Ω
        public double Vout { get; set; }      // Vrms
        public double Iout { get; set; }      // Arms
        public double VSWR { get; set; }
    }

    /// <summary>
    /// 각 스텝에 대한 이상탐지 결과.
    /// </summary>
    public class AnomalyResult
    {
        public int Step { get; set; }
        public double ScoreDelta { get; set; }   // Method A 점수 (0~1)
        public double ScoreCusum { get; set; }    // Method D 점수 (0~1)
        public double AnomalyScore { get; set; }  // 가중 평균 최종 점수 (0~1)
        public bool IsAbnormal { get; set; }
        public string Label => IsAbnormal ? "ABNORMAL" : "NORMAL";
    }

    public static class ImpedanceAnomalyDetector
    {
        /// <summary>
        /// Method A: 인접 스텝 간 Γ(R+jX 근사) 이동거리의 Z-score.
        /// 정확한 반사계수를 쓰려면 NormalizeToGamma()로 먼저 정규화하는 것을 권장합니다.
        /// </summary>
        public static double[] ComputeStepDeltaZScore(IReadOnlyList<ImpedanceStepData> steps)
        {
            int n = steps.Count;
            var gamma = steps.Select(s => new Complex(s.R, s.X)).ToArray();

            var delta = new double[n];
            delta[0] = 0.0; // 첫 스텝은 이전 값이 없으므로 0 (Python의 prepend=gamma[0]과 동일)
            for (int i = 1; i < n; i++)
                delta[i] = Complex.Abs(gamma[i] - gamma[i - 1]);

            double mean = delta.Average();
            double std = StdDev(delta, mean) + 1e-9;

            var score = new double[n];
            for (int i = 0; i < n; i++)
            {
                double z = (delta[i] - mean) / std;
                score[i] = Clamp(z / 3.0, 0.0, 1.0); // 3-sigma 기준 정규화
            }
            return score;
        }

        /// <summary>
        /// Method D: CUSUM(누적합) 변화점 탐지.
        /// field 선택자로 VSWR, R, X 등 어떤 수치 필드든 넣을 수 있습니다.
        /// k = 민감도(슬랙), h = 경보 임계값. 값이 작을수록 더 민감하게 반응합니다.
        /// </summary>
        public static double[] ComputeCusum(
            IReadOnlyList<ImpedanceStepData> steps,
            Func<ImpedanceStepData, double> field,
            double k = 0.5,
            double h = 4.0)
        {
            int n = steps.Count;
            var x = steps.Select(field).ToArray();

            double mean = x.Average();
            double std = StdDev(x, mean) + 1e-9;
            var z = x.Select(v => (v - mean) / std).ToArray();

            var pos = new double[n];
            var neg = new double[n];
            for (int i = 1; i < n; i++)
            {
                pos[i] = Math.Max(0.0, pos[i - 1] + z[i] - k);
                neg[i] = Math.Min(0.0, neg[i - 1] + z[i] + k);
            }

            var score = new double[n];
            for (int i = 0; i < n; i++)
            {
                double cusum = Math.Max(pos[i], -neg[i]);
                score[i] = Clamp(cusum / h, 0.0, 1.0);
            }
            return score;
        }

        /// <summary>
        /// Method A + Method D를 가중 평균하여 최종 이상 스코어와 라벨을 산출합니다.
        /// 데이터가 더 쌓이면 여기에 Method B(Mahalanobis), C(Isolation Forest) 점수를
        /// 추가로 곱-가중하면 됩니다 (Python 프로토타입 참고).
        /// </summary>
        public static List<AnomalyResult> DetectAnomalies(
            IReadOnlyList<ImpedanceStepData> steps,
            double weightDelta = 0.55,
            double weightCusum = 0.45,
            double threshold = 0.5,
            Func<ImpedanceStepData, double> cusumField = null)
        {
            if (steps == null || steps.Count == 0)
                return new List<AnomalyResult>();

            cusumField ??= s => s.VSWR;

            double wSum = weightDelta + weightCusum;
            double wA = weightDelta / wSum;
            double wD = weightCusum / wSum;

            var scoreA = ComputeStepDeltaZScore(steps);
            var scoreD = ComputeCusum(steps, cusumField);

            var results = new List<AnomalyResult>(steps.Count);
            for (int i = 0; i < steps.Count; i++)
            {
                double final = wA * scoreA[i] + wD * scoreD[i];
                results.Add(new AnomalyResult
                {
                    Step = steps[i].Step,
                    ScoreDelta = scoreA[i],
                    ScoreCusum = scoreD[i],
                    AnomalyScore = final,
                    IsAbnormal = final >= threshold
                });
            }
            return results;
        }

        /// <summary>
        /// Method A + Method D를 가중 평균하여 최종 이상 스코어와 라벨을 산출합니다.
        /// 데이터가 더 쌓이면 여기에 Method B(Mahalanobis), C(Isolation Forest) 점수를
        /// 추가로 곱-가중하면 됩니다 (Python 프로토타입 참고).
        /// </summary>
        public static List<AnomalyResult> DetectAnomaliesAI(
            IReadOnlyList<ImpedanceStepData> steps,
            double weightDelta = 0.55,
            double weightCusum = 0.45,
            double threshold = 0.5,
            Func<ImpedanceStepData, double> cusumField = null)
        {
            if (steps == null || steps.Count == 0)
                return new List<AnomalyResult>();

            cusumField ??= s => s.VSWR;

            double wSum = weightDelta + weightCusum;
            double wA = weightDelta / wSum;
            double wD = weightCusum / wSum;

            var scoreA = ComputeStepDeltaZScore(steps);
            var scoreD = ComputeCusum(steps, cusumField);

            var results = new List<AnomalyResult>(steps.Count);
            for (int i = 0; i < steps.Count; i++)
            {
                double final = wA * scoreA[i] + wD * scoreD[i];
                results.Add(new AnomalyResult
                {
                    Step = steps[i].Step,
                    ScoreDelta = scoreA[i],
                    ScoreCusum = scoreD[i],
                    AnomalyScore = final,
                    IsAbnormal = final >= threshold
                });
            }
            return results;
        }

        /// <summary>
        /// 골든 런(정상 확인된) run_id 목록을 받아 threshold를 캘리브레이션합니다.
        /// DB 조회는 MeasurementDb.GetImpedanceStepsByRunId()를 사용합니다.
        /// </summary>
        public static double CalibrateThresholdFromGoldenRuns(
            IEnumerable<long> goldenRunIds,
            string channel,
            double percentile = 97.0)
        {
            var allScores = new List<double>();

            foreach (var runId in goldenRunIds)
            {
                var steps = MeasurementDb.GetImpedanceStepsByRunId(runId, channel);
                if (steps.Count < 2) continue; // Method A/D는 스텝 델타 계산이라 최소 2개 필요

                // threshold를 극단값(999)으로 줘서 라벨링은 의미 없게 만들고 점수만 취함
                var results = DetectAnomaliesAI(steps, threshold: 999);

                // 첫 스텝은 delta=0으로 인위적으로 낮게 잡히므로(비교 대상 없음) 캘리브레이션에서 제외 권장
                allScores.AddRange(results.Skip(1).Select(r => r.AnomalyScore));
            }

            return CalculatePercentile(allScores, percentile);
        }

        // ----------------------------------------------------------------
        // Threshold 캘리브레이션 (골든 런 데이터 기반 percentile 계산)
        // ----------------------------------------------------------------

        /// <summary>
        /// 점수 리스트에서 지정한 percentile 값을 선형보간(linear interpolation) 방식으로 계산.
        /// (numpy.percentile 기본 방식과 동일한 계산법)
        /// </summary>
        public static double CalculatePercentile(IEnumerable<double> scores, double percentile)
        {
            var sorted = scores.OrderBy(v => v).ToList();
            if (sorted.Count == 0) return 0.5; // 데이터 없으면 기본값
            if (sorted.Count == 1) return sorted[0];

            double rank = (percentile / 100.0) * (sorted.Count - 1);
            int lo = (int)Math.Floor(rank);
            int hi = (int)Math.Ceiling(rank);
            if (lo == hi) return sorted[lo];

            double frac = rank - lo;
            return sorted[lo] + frac * (sorted[hi] - sorted[lo]);
        }

        /// <summary>
        /// (선택) Z = R + jX 를 표준 Z0 기준 반사계수 Γ = (Z-Z0)/(Z+Z0) 로 정규화.
        /// 스미스 차트 좌표와 정확히 일치시키려면 ComputeStepDeltaZScore 호출 전에
        /// R, X 대신 이 값의 Real/Imaginary를 넣어 사용하는 것을 권장합니다.
        /// </summary>
        public static Complex NormalizeToGamma(double r, double x, double z0 = 50.0)
        {
            var z = new Complex(r, x);
            return (z - z0) / (z + z0);
        }

        private static double StdDev(IReadOnlyList<double> values, double mean)
        {
            if (values.Count == 0) return 0.0;
            double sumSq = values.Sum(v => (v - mean) * (v - mean));
            return Math.Sqrt(sumSq / values.Count); // population std (numpy 기본값과 동일, ddof=0)
        }

        private static double Clamp(double v, double min, double max) =>
            v < min ? min : (v > max ? max : v);


    }

    // ==========================================================================
    // 데모 / 단위 테스트용 실행 예제
    // Iruza WinForms 프로젝트에서는 이 Program 클래스는 제외하고
    // ImpedanceAnomalyDetector 클래스만 참조하면 됩니다.
    // ==========================================================================
    public class Demo
    {
        public string  Run(List<ImpedanceStepData> pImpedanceStepData, double pweightDelta,double pweightCusum,double pthreshold)
        {
            // Python 샘플 데이터(Bias 궤적)와 동일한 값 - Step 7이 이상치여야 함
            var results = ImpedanceAnomalyDetector.DetectAnomalies(pImpedanceStepData, pweightDelta, pweightCusum, pthreshold);

            Console.WriteLine($"{"Step",5} {"ScoreDelta",12} {"ScoreCusum",12} {"AnomalyScore",13} {"Label",10}");
            foreach (var r in results)
            {
                Console.WriteLine(
                    $"{r.Step,5} {r.ScoreDelta,12:F4} {r.ScoreCusum,12:F4} {r.AnomalyScore,13:F4} {r.Label,10}");

                if(r.Label == "ABNORMAL")
                {
                    return "ABNORMAL";
                }
            }
            return "NORMAL";
        }
        public void Learning(List<ImpedanceStepData> pImpedanceStepData)
        {
            // Python 샘플 데이터(Bias 궤적)와 동일한 값 - Step 7이 이상치여야 함
            var steps = new List<ImpedanceStepData>
            {
                new ImpedanceStepData { Step = 1, R = 20.7, X =  0.39, Vout =  5.39, Iout = 0.26, VSWR = 2.412 },
                new ImpedanceStepData { Step = 2, R = 22.9, X = -0.48, Vout = 25.24, Iout = 1.10, VSWR = 2.180 },
                new ImpedanceStepData { Step = 3, R = 22.6, X =  0.78, Vout = 23.01, Iout = 1.02, VSWR = 2.218 },
                new ImpedanceStepData { Step = 4, R = 24.9, X =  0.35, Vout = 26.63, Iout = 1.07, VSWR = 2.009 },
                new ImpedanceStepData { Step = 5, R = 26.5, X =  0.86, Vout = 26.40, Iout = 0.99, VSWR = 1.888 },
                new ImpedanceStepData { Step = 6, R = 26.1, X = -1.72, Vout = 25.66, Iout = 0.98, VSWR = 1.917 },
                new ImpedanceStepData { Step = 7, R = 12.8, X =  0.11, Vout =  0.51, Iout = 0.04, VSWR = 3.922 }, // 이상치
                new ImpedanceStepData { Step = 8, R = 27.4, X =  0.29, Vout =  4.39, Iout = 0.16, VSWR = 1.823 },
                new ImpedanceStepData { Step = 9, R = 18.2, X =  0.21, Vout =  4.55, Iout = 0.25, VSWR = 2.747 },
            };

            var results = ImpedanceAnomalyDetector.DetectAnomaliesAI(pImpedanceStepData);

            Console.WriteLine($"{"Step",5} {"ScoreDelta",12} {"ScoreCusum",12} {"AnomalyScore",13} {"Label",10}");
            foreach (var r in results)
            {
                Console.WriteLine(
                    $"{r.Step,5} {r.ScoreDelta,12:F4} {r.ScoreCusum,12:F4} {r.AnomalyScore,13:F4} {r.Label,10}");
            }
        }

        //public static void Main() => Run();
    }
}
