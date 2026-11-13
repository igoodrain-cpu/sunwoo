// =====================================================================================
//  Iruza.Diagnostics.Anomaly
//  Robust Mahalanobis(FastMCD) + Extended Isolation Forest 앙상블 — 2년차 WP4(WBS ⑦)
//
//  구성
//   1) RobustScaler          : median / MAD 기반 특성 스케일링 (이상치에 강건)
//   2) RobustMahalanobis     : FastMCD(C-step) + 일치성 보정 + 재가중 → 강건 위치·공분산
//                              → 변수별 기여도(c_i = z_i·(Σ⁻¹z)_i, Σc_i = d²) 제공
//   3) IsolationForest       : Extended IF(랜덤 초평면 분할) — 축 평행 분할의 비선형 사각지대 보완
//                              ExtensionLevel = 0 이면 표준 IF
//   4) EnsembleModel         : Golden Run 보정 세트로 점수 정규화(robust z) → Score Fusion
//                              (가중 평균 / OR 투표 / AND 투표), 목표 오탐률(FPR) 기준 임계값
//   5) StepAwareDetector     : Recipe·Step별 모델 + 표본 부족 시 GLOBAL 모델로 대체, JSON(gzip) 저장/로드
//   6) PolyResidualFeature   : (WP6 연계) Golden Run에서 target ≈ poly(reference) 관계를 학습한 '궤적 잔차'
//                              → 보조 검출기로 보정 Max 결합에 참여, 정상 궤적 안·밖의 비선형 이탈을 포착
//
//  외부 패키지 없음(System.Text.Json만 사용). .NET Core 3.1 / .NET 5~8 / .NET Framework 4.7.2+(System.Text.Json NuGet)
//  어디서나 컴파일되도록 record / init / file-scoped namespace, System.Text.Json 5.0+ 전용 API는 쓰지 않았다.
// =====================================================================================
using System;
using System.Collections.Generic;
using System.IO;
using System.IO.Compression;
using System.Linq;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;

namespace Iruza.Diagnostics.Anomaly
{
    #region ───────── 수치 유틸 ─────────

    internal static class Stat
    {
        public static double Median(IList<double> v)
        {
            var a = v.ToArray();
            Array.Sort(a);
            int n = a.Length;
            if (n == 0) return double.NaN;
            return n % 2 == 1 ? a[n / 2] : 0.5 * (a[n / 2 - 1] + a[n / 2]);
        }

        /// <summary>정규분포 일치성 상수(1.4826)를 곱한 MAD</summary>
        public static double Mad(IList<double> v, double med)
        {
            var dev = new double[v.Count];
            for (int i = 0; i < v.Count; i++) dev[i] = Math.Abs(v[i] - med);
            return 1.4826 * Median(dev);
        }

        public static double StdDev(IList<double> v)
        {
            double m = v.Average();
            return Math.Sqrt(v.Sum(x => (x - m) * (x - m)) / Math.Max(1, v.Count - 1));
        }

        /// <summary>선형 보간 분위수</summary>
        public static double Quantile(IList<double> v, double q)
        {
            var a = v.ToArray();
            Array.Sort(a);
            if (a.Length == 1) return a[0];
            double pos = q * (a.Length - 1);
            int lo = (int)Math.Floor(pos);
            int hi = Math.Min(lo + 1, a.Length - 1);
            return a[lo] + (pos - lo) * (a[hi] - a[lo]);
        }

        /// <summary>
        /// 임계값용 상측 분위수. 꼬리 표본이 충분하면(n·(1−q) ≥ 10) 경험적 분위수,
        /// 부족하면 conformal 순서통계량 ⌈(n+1)q⌉번째 값(n을 넘으면 최댓값)을 쓴다 → 기대 오탐률 ≤ 1−q.
        /// 보정 표본이 적을 때 경험적 분위수(보간)를 그대로 쓰면 임계값이 낮게 잡혀 오탐률이 목표를 넘는다.
        /// </summary>
        public static double TailQuantile(IList<double> v, double q)
        {
            int n = v.Count;
            if (n * (1 - q) >= 10 || n < 10) return Quantile(v, q);
            var a = v.ToArray();
            Array.Sort(a);
            int k = Math.Min(n, (int)Math.Ceiling((n + 1) * q));   // 1-based
            return a[k - 1];
        }

        /// <summary>ROC-AUC (Mann–Whitney U, 동점 평균순위 처리). label 1 = 이상</summary>
        public static double Auc(IList<double> scores, IList<int> labels)
        {
            int n = scores.Count;
            var idx = Enumerable.Range(0, n).OrderBy(i => scores[i]).ToArray();
            var ranks = new double[n];
            int i0 = 0;
            while (i0 < n)
            {
                int j = i0;
                while (j + 1 < n && scores[idx[j + 1]] == scores[idx[i0]]) j++;
                double r = (i0 + j) / 2.0 + 1.0;
                for (int k = i0; k <= j; k++) ranks[idx[k]] = r;
                i0 = j + 1;
            }
            double nPos = 0, sumPos = 0;
            for (int i = 0; i < n; i++)
                if (labels[i] == 1) { nPos++; sumPos += ranks[i]; }
            double nNeg = n - nPos;
            if (nPos == 0 || nNeg == 0) return double.NaN;
            return (sumPos - nPos * (nPos + 1) / 2.0) / (nPos * nNeg);
        }
    }

    internal static class ChiSquare
    {
        public static double Cdf(double x, int k) => x <= 0 ? 0.0 : RegLowerGamma(k / 2.0, x / 2.0);

        public static double Quantile(double p, int k)
        {
            double lo = 0, hi = Math.Max(1.0, k);
            while (Cdf(hi, k) < p) hi *= 2;
            for (int i = 0; i < 200; i++)
            {
                double mid = 0.5 * (lo + hi);
                if (Cdf(mid, k) < p) lo = mid; else hi = mid;
            }
            return 0.5 * (lo + hi);
        }

        // 정칙화 하부 불완전 감마 P(a, x) — 급수 / 연분수 (Numerical Recipes)
        private static double RegLowerGamma(double a, double x)
        {
            double lnPre = -x + a * Math.Log(x) - LogGamma(a);
            if (x < a + 1)
            {
                double ap = a, sum = 1.0 / a, term = sum;
                for (int n = 0; n < 1000; n++)
                {
                    ap += 1; term *= x / ap; sum += term;
                    if (Math.Abs(term) < Math.Abs(sum) * 1e-15) break;
                }
                return sum * Math.Exp(lnPre);
            }
            double b = x + 1 - a, c = 1e300, d = 1 / b, h = d;
            for (int i = 1; i < 1000; i++)
            {
                double an = -i * (i - a);
                b += 2;
                d = an * d + b; if (Math.Abs(d) < 1e-300) d = 1e-300;
                c = b + an / c; if (Math.Abs(c) < 1e-300) c = 1e-300;
                d = 1 / d;
                double del = d * c;
                h *= del;
                if (Math.Abs(del - 1) < 1e-15) break;
            }
            return 1.0 - Math.Exp(lnPre) * h;
        }

        private static readonly double[] LanczosCof =
            { 76.18009172947146, -86.50532032941677, 24.01409824083091,
              -1.231739572450155, 0.1208650973866179e-2, -0.5395239384953e-5 };

        private static double LogGamma(double x)
        {
            double y = x, tmp = x + 5.5;
            tmp -= (x + 0.5) * Math.Log(tmp);
            double ser = 1.000000000190015;
            for (int j = 0; j < 6; j++) ser += LanczosCof[j] / ++y;
            return -tmp + Math.Log(2.5066282746310005 * ser / x);
        }
    }

    internal static class LinAlg
    {
        public static double[] Mean(IReadOnlyList<double[]> X, IList<int> idx)
        {
            int p = X[0].Length;
            var mu = new double[p];
            foreach (int i in idx)
                for (int j = 0; j < p; j++) mu[j] += X[i][j];
            for (int j = 0; j < p; j++) mu[j] /= idx.Count;
            return mu;
        }

        /// <summary>최우추정(1/m) 공분산 — 스케일은 이후 일치성 보정에서 맞춘다</summary>
        public static double[,] Cov(IReadOnlyList<double[]> X, IList<int> idx, double[] mu)
        {
            int p = mu.Length;
            var c = new double[p, p];
            var z = new double[p];
            foreach (int i in idx)
            {
                for (int j = 0; j < p; j++) z[j] = X[i][j] - mu[j];
                for (int a = 0; a < p; a++)
                    for (int b = 0; b <= a; b++) c[a, b] += z[a] * z[b];
            }
            for (int a = 0; a < p; a++)
                for (int b = 0; b <= a; b++)
                {
                    c[a, b] /= idx.Count;
                    c[b, a] = c[a, b];
                }
            return c;
        }

        /// <summary>Cholesky 분해. 특이(공선성) 행렬이면 대각에 ridge를 점증 추가</summary>
        public static double[,] Cholesky(double[,] A, out double ridge)
        {
            int p = A.GetLength(0);
            double trace = 0;
            for (int i = 0; i < p; i++) trace += A[i, i];
            double scale = trace > 0 ? trace / p : 1.0;
            ridge = 0;
            for (int attempt = 0; attempt < 15; attempt++)
            {
                var L = new double[p, p];
                bool ok = true;
                for (int i = 0; i < p && ok; i++)
                {
                    for (int j = 0; j <= i; j++)
                    {
                        double sum = A[i, j] + (i == j ? ridge : 0.0);
                        for (int k = 0; k < j; k++) sum -= L[i, k] * L[j, k];
                        if (i == j)
                        {
                            if (sum <= 1e-12 * scale) { ok = false; break; }
                            L[i, i] = Math.Sqrt(sum);
                        }
                        else L[i, j] = sum / L[j, j];
                    }
                }
                if (ok) return L;
                ridge = ridge == 0 ? 1e-9 * scale : ridge * 10;
            }
            throw new InvalidOperationException("공분산 행렬을 분해할 수 없습니다(상수 특성 또는 표본 부족).");
        }

        public static double LogDet(double[,] L)
        {
            double s = 0;
            for (int i = 0; i < L.GetLength(0); i++) s += Math.Log(L[i, i]);
            return 2 * s;
        }

        /// <summary>d² = ||L⁻¹(x-μ)||² (전진대입)</summary>
        public static double MahalanobisSq(double[,] L, double[] mu, double[] x)
        {
            int p = mu.Length;
            var y = new double[p];
            double d2 = 0;
            for (int i = 0; i < p; i++)
            {
                double s = x[i] - mu[i];
                for (int k = 0; k < i; k++) s -= L[i, k] * y[k];
                y[i] = s / L[i, i];
                d2 += y[i] * y[i];
            }
            return d2;
        }

        /// <summary>하삼각 L의 역행렬 (역시 하삼각)</summary>
        public static double[][] InverseLower(double[,] L)
        {
            int p = L.GetLength(0);
            var inv = new double[p][];
            for (int i = 0; i < p; i++) inv[i] = new double[p];
            for (int c = 0; c < p; c++)
                for (int i = c; i < p; i++)
                {
                    double s = i == c ? 1.0 : 0.0;
                    for (int k = c; k < i; k++) s -= L[i, k] * inv[k][c];
                    inv[i][c] = s / L[i, i];
                }
            return inv;
        }

        public static double[][] InverseFromCholesky(double[,] L)
        {
            int p = L.GetLength(0);
            var inv = new double[p][];
            for (int c = 0; c < p; c++)
            {
                // L y = e_c
                var y = new double[p];
                for (int i = 0; i < p; i++)
                {
                    double s = i == c ? 1.0 : 0.0;
                    for (int k = 0; k < i; k++) s -= L[i, k] * y[k];
                    y[i] = s / L[i, i];
                }
                // Lᵀ x = y
                var x = new double[p];
                for (int i = p - 1; i >= 0; i--)
                {
                    double s = y[i];
                    for (int k = i + 1; k < p; k++) s -= L[k, i] * x[k];
                    x[i] = s / L[i, i];
                }
                for (int r = 0; r < p; r++)
                {
                    if (inv[r] == null) inv[r] = new double[p];
                    inv[r][c] = x[r];
                }
            }
            return inv;
        }
    }

    #endregion

    #region ───────── 1) RobustScaler ─────────

    public sealed class RobustScaler
    {
        public double[] Center { get; set; }
        public double[] Scale { get; set; }

        public static RobustScaler Fit(IReadOnlyList<double[]> X)
        {
            int p = X[0].Length;
            var s = new RobustScaler { Center = new double[p], Scale = new double[p] };
            for (int j = 0; j < p; j++)
            {
                var col = X.Select(r => r[j]).ToArray();
                double med = Stat.Median(col);
                double mad = Stat.Mad(col, med);
                if (mad < 1e-12) mad = Stat.StdDev(col);
                if (mad < 1e-12) mad = 1.0;            // 상수 특성
                s.Center[j] = med;
                s.Scale[j] = mad;
            }
            return s;
        }

        public double[] Transform(double[] x)
        {
            var z = new double[x.Length];
            for (int j = 0; j < x.Length; j++) z[j] = (x[j] - Center[j]) / Scale[j];
            return z;
        }
    }

    #endregion

    #region ───────── 2) Robust Mahalanobis (FastMCD) ─────────

    public sealed class McdOptions
    {
        /// <summary>false면 고전적 표본 공분산(비교용)</summary>
        public bool UseMcd { get; set; } = true;
        /// <summary>
        /// h/n. 기본 0.75 → 오염 25%까지 견디면서 운전 범위 끝단(정상)을 잘라내지 않음.
        /// null이면 (n+p+1)/2 → 최대 붕괴점(≈50%)이지만, 비타원형 정상 분포에서는 정상 끝단을 이상치로 취급해
        /// 보정 임계값이 올라가고 검출률이 떨어진다(데모에서 확인).
        /// </summary>
        public double? SupportFraction { get; set; } = 0.75;
        public int NumStarts { get; set; } = 500;
        public int NumBest { get; set; } = 10;
        public bool Reweight { get; set; } = true;
        public int Seed { get; set; } = 42;
        /// <summary>
        /// 스케일된 공간의 분산 하한. 레시피상 거의 고정인 특성(가스 유량 설정값 등)에서
        /// 공분산이 특이해져 미세한 흔들림이 거대한 거리로 튀는 것을 막는다.
        /// </summary>
        public double MinVariance { get; set; } = 1e-4;
    }

    public sealed class RobustMahalanobis
    {
        public int Dim { get; set; }
        public bool IsRobust { get; set; }
        public int SupportSize { get; set; }
        public double[] Location { get; set; }
        /// <summary>Σ⁻¹ — 배포 시에는 Location·Precision만 있으면 점수 계산 가능</summary>
        public double[][] Precision { get; set; }
        /// <summary>백색화 행렬 W = L⁻¹ (Σ = LLᵀ). y = W(x−μ) 이면 ||y||² = d²</summary>
        public double[][] Whitening { get; set; }

        /// <summary>강건 공분산으로 상관을 제거한 좌표 — IF 입력으로 쓰면 IF가 비선형 구조에만 집중</summary>
        public double[] Whiten(double[] x)
        {
            var y = new double[Dim];
            for (int i = 0; i < Dim; i++)
            {
                double s = 0;
                for (int j = 0; j <= i; j++) s += Whitening[i][j] * (x[j] - Location[j]);
                y[i] = s;
            }
            return y;
        }

        public double DistanceSq(double[] x)
        {
            double d2 = 0;
            var z = Center(x);
            for (int i = 0; i < Dim; i++)
            {
                double pz = 0;
                for (int j = 0; j < Dim; j++) pz += Precision[i][j] * z[j];
                d2 += z[i] * pz;
            }
            return Math.Max(0, d2);
        }

        /// <summary>변수별 기여도 c_i = z_i·(Σ⁻¹z)_i  (Σ c_i = d², 음수 가능 = 다른 변수가 설명해주는 몫)</summary>
        public double[] Contributions(double[] x)
        {
            var z = Center(x);
            var c = new double[Dim];
            for (int i = 0; i < Dim; i++)
            {
                double pz = 0;
                for (int j = 0; j < Dim; j++) pz += Precision[i][j] * z[j];
                c[i] = z[i] * pz;
            }
            return c;
        }

        /// <summary>정규 가정 시 χ²(p) 상측 확률</summary>
        public double PValue(double d2) => 1.0 - ChiSquare.Cdf(d2, Dim);

        private double[] Center(double[] x)
        {
            var z = new double[Dim];
            for (int i = 0; i < Dim; i++) z[i] = x[i] - Location[i];
            return z;
        }

        private sealed class Candidate
        {
            public double[] Mu;
            public double[,] Cov;
            public double LogDet;
        }

        public static RobustMahalanobis Fit(IReadOnlyList<double[]> X, McdOptions opt)
        {
            int n = X.Count, p = X[0].Length;
            if (n < 2 * (p + 1)) throw new ArgumentException($"표본이 너무 적습니다 (n={n}, p={p}).");
            var all = Enumerable.Range(0, n).ToArray();

            double[] mu;
            double[,] cov;
            int support = n;

            if (!opt.UseMcd)
            {
                mu = LinAlg.Mean(X, all);
                cov = LinAlg.Cov(X, all, mu);
            }
            else
            {
                int h = opt.SupportFraction.HasValue
                    ? (int)Math.Ceiling(opt.SupportFraction.Value * n)
                    : (n + p + 1) / 2;
                h = Math.Max(p + 1, Math.Min(n, h));

                // ① 무작위 (p+1)-부분집합에서 출발 → C-step 2회
                var rng = new Random(opt.Seed);
                var cands = new List<Candidate>(opt.NumStarts);
                for (int s = 0; s < opt.NumStarts; s++)
                {
                    var sub = SampleWithoutReplacement(rng, n, p + 1);
                    var m0 = LinAlg.Mean(X, sub);
                    var c0 = LinAlg.Cov(X, sub, m0);
                    cands.Add(CSteps(X, m0, c0, h, 2));
                }
                // ② 상위 NumBest개만 수렴까지 C-step → 최소 행렬식 해
                var best = cands.OrderBy(c => c.LogDet)
                                .Take(opt.NumBest)
                                .Select(c => CSteps(X, c.Mu, c.Cov, h, 100))
                                .OrderBy(c => c.LogDet)
                                .First();
                mu = best.Mu;
                cov = best.Cov;
                support = h;

                // ③ 일치성 보정: 정상분포에서 d²의 중앙값이 χ²_p(0.5)가 되도록 스케일
                double chiMed = ChiSquare.Quantile(0.5, p);
                ScaleInPlace(cov, Stat.Median(Distances(X, mu, cov)) / chiMed);

                // ④ 재가중: χ²_p(0.975) 이내 점으로 재추정 → 효율(분산) 회복
                if (opt.Reweight)
                {
                    var d2 = Distances(X, mu, cov);
                    double cut = ChiSquare.Quantile(0.975, p);
                    var keep = all.Where(i => d2[i] <= cut).ToArray();
                    if (keep.Length > 2 * (p + 1))
                    {
                        mu = LinAlg.Mean(X, keep);
                        cov = LinAlg.Cov(X, keep, mu);
                        support = keep.Length;
                        // 절단으로 과소추정된 스케일을 강건하게(중앙값 기반) 재보정
                        ScaleInPlace(cov, Stat.Median(Distances(X, mu, cov)) / chiMed);
                    }
                }
            }

            for (int i = 0; i < p; i++)
                if (cov[i, i] < opt.MinVariance) cov[i, i] = opt.MinVariance;

            double ridge;
            var L = LinAlg.Cholesky(cov, out ridge);
            return new RobustMahalanobis
            {
                Dim = p,
                IsRobust = opt.UseMcd,
                SupportSize = support,
                Location = mu,
                Precision = LinAlg.InverseFromCholesky(L),
                Whitening = LinAlg.InverseLower(L)
            };
        }

        private static Candidate CSteps(IReadOnlyList<double[]> X, double[] mu, double[,] cov, int h, int maxSteps)
        {
            Candidate cur = null;
            for (int s = 0; s < maxSteps; s++)
            {
                double ridge;
                var L = LinAlg.Cholesky(cur == null ? cov : cur.Cov, out ridge);
                var m = cur == null ? mu : cur.Mu;
                int n = X.Count;
                var d2 = new double[n];
                var order = new int[n];
                for (int i = 0; i < n; i++) { d2[i] = LinAlg.MahalanobisSq(L, m, X[i]); order[i] = i; }
                Array.Sort(d2, order);
                var hIdx = new int[h];
                Array.Copy(order, hIdx, h);

                var nm = LinAlg.Mean(X, hIdx);
                var nc = LinAlg.Cov(X, hIdx, nm);
                var next = new Candidate { Mu = nm, Cov = nc, LogDet = LinAlg.LogDet(LinAlg.Cholesky(nc, out ridge)) };

                // C-step은 det를 증가시키지 않는다 → 감소가 멈추면 수렴
                if (cur != null && next.LogDet >= cur.LogDet - 1e-12) break;
                cur = next;
            }
            return cur;
        }

        private static double[] Distances(IReadOnlyList<double[]> X, double[] mu, double[,] cov)
        {
            double ridge;
            var L = LinAlg.Cholesky(cov, out ridge);
            var d = new double[X.Count];
            for (int i = 0; i < X.Count; i++) d[i] = LinAlg.MahalanobisSq(L, mu, X[i]);
            return d;
        }

        private static void ScaleInPlace(double[,] c, double f)
        {
            if (!(f > 0) || double.IsInfinity(f)) return;
            for (int i = 0; i < c.GetLength(0); i++)
                for (int j = 0; j < c.GetLength(1); j++) c[i, j] *= f;
        }

        internal static int[] SampleWithoutReplacement(Random rng, int n, int k)
        {
            var pool = Enumerable.Range(0, n).ToArray();
            for (int i = 0; i < k; i++)
            {
                int j = i + rng.Next(n - i);
                int t = pool[i]; pool[i] = pool[j]; pool[j] = t;
            }
            var r = new int[k];
            Array.Copy(pool, r, k);
            return r;
        }
    }

    #endregion

    #region ───────── 3) (Extended) Isolation Forest ─────────

    public sealed class IForestOptions
    {
        public int NumTrees { get; set; } = 100;
        public int SampleSize { get; set; } = 256;
        /// <summary>0 = 표준 IF(축 평행), p-1 = 완전 확장(임의 방향 초평면), -1 = 자동(p-1)</summary>
        public int ExtensionLevel { get; set; } = -1;
        public int Seed { get; set; } = 1234;
    }

    public sealed class IsoNode
    {
        /// <summary>분할 초평면 법선 (리프면 null)</summary>
        public double[] Normal { get; set; }
        /// <summary>초평면 통과점 (리프면 null)</summary>
        public double[] Point { get; set; }
        public IsoNode Left { get; set; }
        public IsoNode Right { get; set; }
        /// <summary>리프에 남은 학습 표본 수</summary>
        public int Size { get; set; }

        [JsonIgnore] public bool IsLeaf => Left == null;
    }

    public sealed class IsolationForest
    {
        public int Dim { get; set; }
        public int SampleSize { get; set; }
        public int ExtensionLevel { get; set; }
        public List<IsoNode> Trees { get; set; } = new List<IsoNode>();

        public static IsolationForest Fit(IReadOnlyList<double[]> X, IForestOptions opt)
        {
            int n = X.Count, p = X[0].Length;
            int psi = Math.Min(opt.SampleSize, n);
            int ext = opt.ExtensionLevel < 0 ? p - 1 : Math.Min(opt.ExtensionLevel, p - 1);
            int heightLimit = (int)Math.Ceiling(Math.Log(psi, 2));
            var rng = new Random(opt.Seed);

            var f = new IsolationForest { Dim = p, SampleSize = psi, ExtensionLevel = ext };
            for (int t = 0; t < opt.NumTrees; t++)
            {
                var idx = RobustMahalanobis.SampleWithoutReplacement(rng, n, psi);
                var pts = idx.Select(i => X[i]).ToList();
                f.Trees.Add(Build(pts, 0, heightLimit, ext, rng));
            }
            return f;
        }

        /// <summary>이상 점수 s = 2^(−E[h(x)]/c(ψ)) ∈ (0,1). 0.5 부근 = 정상, 1에 가까울수록 이상</summary>
        public double Score(double[] x)
        {
            double sum = 0;
            foreach (var t in Trees) sum += PathLength(t, x);
            return Math.Pow(2.0, -(sum / Trees.Count) / C(SampleSize));
        }

        private static IsoNode Build(List<double[]> pts, int depth, int limit, int ext, Random rng)
        {
            if (depth >= limit || pts.Count <= 1) return new IsoNode { Size = pts.Count };

            int p = pts[0].Length;
            var mins = new double[p];
            var maxs = new double[p];
            for (int j = 0; j < p; j++) { mins[j] = double.MaxValue; maxs[j] = double.MinValue; }
            foreach (var x in pts)
                for (int j = 0; j < p; j++)
                {
                    if (x[j] < mins[j]) mins[j] = x[j];
                    if (x[j] > maxs[j]) maxs[j] = x[j];
                }
            var varying = Enumerable.Range(0, p).Where(j => maxs[j] - mins[j] > 1e-12).ToArray();
            if (varying.Length == 0) return new IsoNode { Size = pts.Count };

            for (int attempt = 0; attempt < 10; attempt++)
            {
                // 법선: (ext+1)개 차원만 N(0,1), 나머지 0  → ext=0이면 축 평행 분할
                int active = Math.Min(ext + 1, varying.Length);
                var dims = RobustMahalanobis.SampleWithoutReplacement(rng, varying.Length, active)
                                            .Select(k => varying[k]).ToArray();
                var normal = new double[p];
                foreach (int j in dims) normal[j] = Gaussian(rng);

                // 통과점: 노드 데이터의 경계 상자 안에서 균등 추출
                var point = new double[p];
                for (int j = 0; j < p; j++) point[j] = mins[j] + rng.NextDouble() * (maxs[j] - mins[j]);

                var left = new List<double[]>();
                var right = new List<double[]>();
                foreach (var x in pts)
                    (Side(normal, point, x) ? left : right).Add(x);

                if (left.Count > 0 && right.Count > 0)
                {
                    return new IsoNode
                    {
                        Normal = normal,
                        Point = point,
                        Size = pts.Count,
                        Left = Build(left, depth + 1, limit, ext, rng),
                        Right = Build(right, depth + 1, limit, ext, rng)
                    };
                }
            }
            return new IsoNode { Size = pts.Count };
        }

        private static bool Side(double[] normal, double[] point, double[] x)
        {
            double s = 0;
            for (int j = 0; j < x.Length; j++)
                if (normal[j] != 0) s += (x[j] - point[j]) * normal[j];
            return s <= 0;
        }

        private static double PathLength(IsoNode node, double[] x)
        {
            int depth = 0;
            while (!node.IsLeaf)
            {
                node = Side(node.Normal, node.Point, x) ? node.Left : node.Right;
                depth++;
            }
            return depth + C(node.Size);
        }

        /// <summary>표본 n개 BST의 평균 실패 탐색 경로 길이</summary>
        private static double C(int n)
        {
            if (n <= 1) return 0;
            if (n == 2) return 1;
            return 2.0 * (Math.Log(n - 1) + 0.5772156649015329) - 2.0 * (n - 1) / n;
        }

        private static double Gaussian(Random rng)
        {
            double u1 = 1.0 - rng.NextDouble(), u2 = rng.NextDouble();
            return Math.Sqrt(-2.0 * Math.Log(u1)) * Math.Cos(2 * Math.PI * u2);
        }
    }

    #endregion

    #region ───────── 4) 앙상블 (Score Fusion) ─────────

    public enum FusionMode
    {
        /// <summary>w·z_MD + (1−w)·z_IF ≥ 임계값. 두 점수가 함께 오를 때 강하지만, 한쪽만 강한 이상은 희석된다</summary>
        WeightedAverage,
        /// <summary>
        /// 보정 Max: max(2w·z_MD/τ_MD, 2(1−w)·z_IF/τ_IF, z_RES/τ_RES) ≥ 임계값 (τ = 각 검출기의 보정 세트 1−FPR 분위수).
        /// 어느 한 검출기만 강하게 반응해도 잡으면서, 결합 임계값을 보정 세트에서 다시 정해 전체 FPR을 목표치로 유지.
        /// 궤적 잔차 검출기(TrajectoryResiduals)는 이 모드에서만 참여한다
        /// </summary>
        CalibratedMax,
        /// <summary>둘 중 하나라도 개별 임계값 초과 (검출률↑, 오탐률 최대 2배)</summary>
        VoteAny,
        /// <summary>둘 다 초과 (오탐률↓, 검출률↓)</summary>
        VoteAll
    }

    public sealed class EnsembleOptions
    {
        public McdOptions Mcd { get; set; } = new McdOptions();
        public IForestOptions Forest { get; set; } = new IForestOptions();
        /// <summary>
        /// true: IF를 MCD 백색화 공간(y = L⁻¹(x−μ))에서 학습.
        /// 선형·상관 이탈 검출은 크게 좋아지지만, 잡음 차원이 신호 차원과 같은 크기로 부풀려져
        /// 비선형 궤적 이탈 검출이 약해진다(IF가 MD의 복제가 됨). 상호보완이 목적이면 false 권장.
        /// </summary>
        public bool ForestOnWhitened { get; set; } = false;
        /// <summary>MD 가중치 w (IF는 1−w). TuneWeight로 검증 세트에서 결정</summary>
        public double WeightMahalanobis { get; set; } = 0.5;
        /// <summary>Golden Run 보정 세트 기준 목표 오탐률 (임계값 = 1−FPR 분위수)</summary>
        public double TargetFpr { get; set; } = 0.01;
        public FusionMode Mode { get; set; } = FusionMode.CalibratedMax;
        public int TopContributors { get; set; } = 3;
        /// <summary>(선택) 궤적 잔차 보조 검출기 정의 — 비어 있으면 MD + IF만 사용</summary>
        public List<ResidualSpec> TrajectoryResiduals { get; set; } = new List<ResidualSpec>();
    }

    public sealed class ResidualSpec
    {
        public string Name { get; set; }
        /// <summary>잔차를 볼 특성 인덱스 (예: x_ohm)</summary>
        public int Target { get; set; }
        /// <summary>기준 특성 인덱스 (예: r_ohm, RF Power, Load position)</summary>
        public int Reference { get; set; }
        public int Degree { get; set; } = 2;
    }

    /// <summary>점수 정규화 — Golden Run 보정 세트의 median / MAD로 robust z 변환</summary>
    public sealed class ScoreNorm
    {
        public double Median { get; set; }
        public double Scale { get; set; }

        public static ScoreNorm Fit(IList<double> s)
        {
            double med = Stat.Median(s);
            double mad = Stat.Mad(s, med);
            if (mad < 1e-12) mad = Stat.StdDev(s);
            if (mad < 1e-12) mad = 1.0;
            return new ScoreNorm { Median = med, Scale = mad };
        }

        public double Z(double s) => (s - Median) / Scale;
    }

    public sealed class Contribution
    {
        public string Feature { get; set; }
        public double Value { get; set; }
        /// <summary>양(+)의 기여 합 대비 비율 (음수 기여 = 다른 변수와의 상관으로 상쇄되는 몫은 0으로 표시)</summary>
        public double Share { get; set; }
        public override string ToString() => $"{Feature} {Share:P0}";
    }

    public sealed class AnomalyResult
    {
        public string ModelKey { get; set; }
        public double MahalanobisSq { get; set; }
        public double MahalanobisPValue { get; set; }
        public double IForestScore { get; set; }
        public double ZMahalanobis { get; set; }
        public double ZIForest { get; set; }
        public double ZResidual { get; set; }
        public double Fused { get; set; }
        public double FusedThreshold { get; set; }
        public bool FlagMahalanobis { get; set; }
        public bool FlagIForest { get; set; }
        public bool FlagResidual { get; set; }
        public bool IsAnomaly { get; set; }
        public List<Contribution> TopContributors { get; set; }

        /// <summary>어느 검출기가 판정을 주도했는지 (Smith Chart 툴팁 표시용)</summary>
        public string Driver
        {
            get
            {
                var d = new List<string>();
                if (FlagMahalanobis) d.Add("MD(선형·상관)");
                if (FlagIForest) d.Add("IF(희소영역)");
                if (FlagResidual) d.Add("궤적잔차");
                if (d.Count > 0) return string.Join("+", d);
                return IsAnomaly ? "Fusion" : "-";
            }
        }

        public override string ToString() =>
            $"[{ModelKey}] {(IsAnomaly ? "이상" : "정상")}  fused={Fused:F2} (thr {FusedThreshold:F2})  " +
            $"zMD={ZMahalanobis:F2} zIF={ZIForest:F2} zRES={ZResidual:F2}  d²={MahalanobisSq:F1} p={MahalanobisPValue:E1}  " +
            $"IF={IForestScore:F3}  주도={Driver}  기여={string.Join(", ", TopContributors)}";
    }

    public sealed class EnsembleModel
    {
        public string Key { get; set; }
        public string[] FeatureNames { get; set; }
        public RobustScaler Scaler { get; set; }
        public RobustMahalanobis Mahalanobis { get; set; }
        public IsolationForest Forest { get; set; }
        public ScoreNorm NormMahalanobis { get; set; }
        public ScoreNorm NormForest { get; set; }
        /// <summary>τ_MD, τ_IF — 각 검출기 z의 보정 세트 1−FPR 분위수</summary>
        public double ThresholdMahalanobis { get; set; }
        public double ThresholdForest { get; set; }
        public double ThresholdAverage { get; set; }
        public double ThresholdMax { get; set; }
        public List<PolyResidualFeature> Residuals { get; set; } = new List<PolyResidualFeature>();
        public ScoreNorm NormResidual { get; set; }
        public double ThresholdResidual { get; set; }
        [JsonIgnore] public bool HasResidual => Residuals != null && Residuals.Count > 0;
        public bool ForestOnWhitened { get; set; }
        public double WeightMahalanobis { get; set; }
        public double TargetFpr { get; set; }
        public FusionMode Mode { get; set; }
        public int TopK { get; set; }
        public int TrainCount { get; set; }

        /// <param name="train">Golden Run 학습 세트 (소량 오염 허용 — MCD가 흡수)</param>
        /// <param name="calib">Golden Run 보정 세트 (학습과 분리된 정상 Run 권장)</param>
        public static EnsembleModel Fit(string key, string[] names,
                                        IReadOnlyList<double[]> train, IReadOnlyList<double[]> calib,
                                        EnsembleOptions opt)
        {
            var m = FitUncalibrated(key, names, train, opt);
            m.Calibrate(calib);
            return m;
        }

        /// <summary>검출기만 학습하고 정규화·임계값은 비워 둔다 (교차 보정에서 사용)</summary>
        public static EnsembleModel FitUncalibrated(string key, string[] names,
                                                    IReadOnlyList<double[]> train, EnsembleOptions opt)
        {
            var m = new EnsembleModel
            {
                Key = key,
                FeatureNames = names,
                ForestOnWhitened = opt.ForestOnWhitened,
                WeightMahalanobis = opt.WeightMahalanobis,
                TargetFpr = opt.TargetFpr,
                Mode = opt.Mode,
                TopK = opt.TopContributors,
                TrainCount = train.Count
            };
            m.Scaler = RobustScaler.Fit(train);
            var xs = train.Select(m.Scaler.Transform).ToList();
            m.Mahalanobis = RobustMahalanobis.Fit(xs, opt.Mcd);
            m.Forest = IsolationForest.Fit(xs.Select(m.ForestInput).ToList(), opt.Forest);
            m.Residuals = opt.TrajectoryResiduals
                             .Select(r => PolyResidualFeature.Fit(train, r.Target, r.Reference, r.Degree, r.Name))
                             .ToList();
            return m;
        }

        /// <summary>정규화 파라미터·임계값을 보정 세트로 다시 산정 (가중치 변경, 기준선 재캘리브레이션 시 호출)</summary>
        public void Calibrate(IReadOnlyList<double[]> calib) => CalibrateRaw(calib.Select(RawScores).ToList());

        /// <summary>
        /// 원점수 (MD 거리, IF 점수, 궤적 잔차)로 정규화·임계값을 산정한다.
        /// 교차 보정에서는 '그 표본을 학습에 쓰지 않은 모델'의 원점수를 넘긴다.
        /// </summary>
        public void CalibrateRaw(IReadOnlyList<Tuple<double, double, double>> raw)
        {
            NormMahalanobis = ScoreNorm.Fit(raw.Select(r => r.Item1).ToList());
            NormForest = ScoreNorm.Fit(raw.Select(r => r.Item2).ToList());

            NormResidual = ScoreNorm.Fit(raw.Select(r => r.Item3).ToList());

            var zMd = raw.Select(r => NormMahalanobis.Z(r.Item1)).ToList();
            var zIf = raw.Select(r => NormForest.Z(r.Item2)).ToList();
            var zRes = raw.Select(r => NormResidual.Z(r.Item3)).ToList();
            double q = 1.0 - TargetFpr;
            ThresholdMahalanobis = Math.Max(1e-6, Stat.TailQuantile(zMd, q));
            ThresholdForest = Math.Max(1e-6, Stat.TailQuantile(zIf, q));
            ThresholdResidual = Math.Max(1e-6, Stat.TailQuantile(zRes, q));
            // 결합 통계량의 임계값도 보정 세트에서 직접 산정 → 결합 후에도 FPR이 목표치로 유지
            ThresholdAverage = Stat.TailQuantile(zMd.Select((z, i) => FuseAverage(z, zIf[i])).ToList(), q);
            ThresholdMax = Stat.TailQuantile(zMd.Select((z, i) => FuseMax(z, zIf[i], zRes[i])).ToList(), q);
        }

        /// <summary>
        /// 라벨된 검증 세트(DOE 이상 조건 + 정상)로 MD 가중치 w를 격자 탐색 후 임계값 재산정.
        /// 목표 = 보정 세트로 정한 임계값(목표 FPR)에서의 검증 검출률(TPR) 최대 — 운영 동작점 기준.
        /// 동률이면 AUC, 그다음 0.5에 가까운 w를 택해 과적합을 줄인다.
        /// </summary>
        public double TuneWeight(IReadOnlyList<double[]> X, IReadOnlyList<int> y,
                                 IReadOnlyList<double[]> calib, double step = 0.05)
        {
            Calibrate(calib);                                   // τ_MD, τ_IF 확정 (w와 무관)
            var zv = X.Select(ZScores).ToList();
            var zc = calib.Select(ZScores).ToList();
            var labels = y.ToList();
            int nPos = labels.Count(l => l == 1);
            double bestW = 0.5, bestTpr = -1, bestAuc = -1;
            for (double w = 0; w <= 1.0 + 1e-9; w += step)
            {
                WeightMahalanobis = w;
                double thr = Stat.TailQuantile(zc.Select(t => FusedScore(t.Item1, t.Item2, t.Item3)).ToList(), 1.0 - TargetFpr);
                var sv = zv.Select(t => FusedScore(t.Item1, t.Item2, t.Item3)).ToList();
                double tpr = Enumerable.Range(0, sv.Count).Count(i => labels[i] == 1 && sv[i] > thr) / (double)nPos;
                double auc = Stat.Auc(sv, labels);
                bool better = tpr > bestTpr + 1e-9 ||
                              (Math.Abs(tpr - bestTpr) <= 1e-9 && (auc > bestAuc + 1e-9 ||
                               (Math.Abs(auc - bestAuc) <= 1e-9 && Math.Abs(w - 0.5) < Math.Abs(bestW - 0.5))));
                if (better) { bestTpr = tpr; bestAuc = auc; bestW = w; }
            }
            WeightMahalanobis = Math.Round(bestW, 4);
            Calibrate(calib);
            return bestTpr;
        }

        public AnomalyResult Diagnose(double[] x)
        {
            var xs = Scaler.Transform(x);
            double d2 = Mahalanobis.DistanceSq(xs);
            double sIf = Forest.Score(ForestInput(xs));
            double zMd = NormMahalanobis.Z(Math.Sqrt(d2));
            double zIf = NormForest.Z(sIf);
            double zRes = NormResidual.Z(ResidualScore(x));
            bool fMd = zMd > ThresholdMahalanobis;
            bool fIf = zIf > ThresholdForest;
            bool fRes = HasResidual && zRes > ThresholdResidual;
            double fused = FusedScore(zMd, zIf, zRes);
            double thr = Mode == FusionMode.WeightedAverage ? ThresholdAverage : ThresholdMax;

            bool isAnomaly;
            switch (Mode)
            {
                case FusionMode.VoteAny: isAnomaly = fMd || fIf; break;
                case FusionMode.VoteAll: isAnomaly = fMd && fIf; break;
                default: isAnomaly = fused > thr; break;
            }

            var c = Mahalanobis.Contributions(xs);
            double posSum = c.Where(v => v > 0).Sum();
            var top = c.Select((v, i) => new Contribution
                       {
                           Feature = FeatureNames[i],
                           Value = v,
                           Share = posSum > 0 ? Math.Max(0, v) / posSum : 0
                       })
                       .OrderByDescending(t => t.Value)
                       .Take(TopK)
                       .ToList();

            return new AnomalyResult
            {
                ModelKey = Key,
                MahalanobisSq = d2,
                MahalanobisPValue = Mahalanobis.PValue(d2),
                IForestScore = sIf,
                ZMahalanobis = zMd,
                ZIForest = zIf,
                ZResidual = HasResidual ? zRes : 0,
                Fused = fused,
                FusedThreshold = thr,
                FlagMahalanobis = fMd,
                FlagIForest = fIf,
                FlagResidual = fRes && Mode == FusionMode.CalibratedMax,
                IsAnomaly = isAnomaly,
                TopContributors = top
            };
        }

        /// <summary>현재 Mode의 결합 점수 (Vote 모드는 순위용으로 Max 통계량 사용)</summary>
        public double FusedScore(double zMd, double zIf, double zRes) =>
            Mode == FusionMode.WeightedAverage ? FuseAverage(zMd, zIf) : FuseMax(zMd, zIf, zRes);

        private double FuseAverage(double zMd, double zIf) =>
            WeightMahalanobis * zMd + (1 - WeightMahalanobis) * zIf;

        private double FuseMax(double zMd, double zIf, double zRes)
        {
            double m = Math.Max(2 * WeightMahalanobis * zMd / ThresholdMahalanobis,
                                2 * (1 - WeightMahalanobis) * zIf / ThresholdForest);
            return HasResidual ? Math.Max(m, zRes / ThresholdResidual) : m;
        }

        /// <summary>궤적 잔차 원점수 = max_k |robust z_k| (원 특성 공간에서 계산)</summary>
        private double ResidualScore(double[] x)
        {
            if (!HasResidual) return 0;
            double s = 0;
            foreach (var r in Residuals) s = Math.Max(s, r.AbsZ(x));
            return s;
        }

        private double[] ForestInput(double[] xs) => ForestOnWhitened ? Mahalanobis.Whiten(xs) : xs;

        /// <summary>(MD 거리 d, IF 점수, 궤적 잔차) — 정규화 전 원점수</summary>
        public Tuple<double, double, double> RawScores(double[] x)
        {
            var xs = Scaler.Transform(x);
            return Tuple.Create(Math.Sqrt(Mahalanobis.DistanceSq(xs)), Forest.Score(ForestInput(xs)), ResidualScore(x));
        }

        private Tuple<double, double, double> ZScores(double[] x)
        {
            var r = RawScores(x);
            return Tuple.Create(NormMahalanobis.Z(r.Item1), NormForest.Z(r.Item2), NormResidual.Z(r.Item3));
        }
    }

    #endregion

    #region ───────── 5) Step-aware 진단기 ─────────

    public sealed class RfSample
    {
        public string Recipe { get; set; }
        public int Step { get; set; }
        public double[] Features { get; set; }
        /// <summary>0 정상 / 1 이상 (검증·튜닝용 라벨)</summary>
        public int Label { get; set; }
        /// <summary>이상 유형 코드 등 (예: "N", "매칭불량")</summary>
        public string Tag { get; set; }
    }

    public sealed class StepAwareDetector
    {
        public string[] FeatureNames { get; set; }
        public Dictionary<string, EnsembleModel> Models { get; set; } = new Dictionary<string, EnsembleModel>();
        /// <summary>Recipe·Step 표본이 부족할 때 쓰는 전체 모델 (다봉 분포라 정밀도는 낮음)</summary>
        public EnsembleModel Global { get; set; }

        public static string KeyOf(string recipe, int step) => recipe + "|" + step;

        /// <param name="minSamplesPerFeature">Step 모델 최소 학습 표본 = 이 값 × 특성 수</param>
        /// <param name="minCalibSamples">Step 모델 최소 보정 표본 (null이면 max(50, 1/FPR))</param>
        public static StepAwareDetector Fit(IEnumerable<RfSample> golden, IEnumerable<RfSample> calib,
                                            string[] names, EnsembleOptions opt, int minSamplesPerFeature = 10,
                                            int? minCalibSamples = null)
        {
            var g = golden.ToList();
            var c = calib.ToList();
            int minTrain = Math.Max(2 * (names.Length + 1), minSamplesPerFeature * names.Length);
            int minCalib = minCalibSamples ?? Math.Max(50, (int)Math.Ceiling(1.0 / opt.TargetFpr));

            var det = new StepAwareDetector { FeatureNames = names };
            det.Global = EnsembleModel.Fit("GLOBAL", names,
                                           g.Select(s => s.Features).ToList(),
                                           c.Select(s => s.Features).ToList(), opt);

            foreach (var grp in g.GroupBy(s => KeyOf(s.Recipe, s.Step)))
            {
                var tr = grp.Select(s => s.Features).ToList();
                var cal = c.Where(s => KeyOf(s.Recipe, s.Step) == grp.Key).Select(s => s.Features).ToList();
                if (tr.Count < minTrain || cal.Count < minCalib) continue;   // → GLOBAL로 대체
                det.Models[grp.Key] = EnsembleModel.Fit(grp.Key, names, tr, cal, opt);
            }
            return det;
        }

        /// <summary>
        /// 교차 보정(cross-fitting) 학습 — Golden 표본이 적을 때 권장.
        /// 표본을 그룹(Run) 단위로 K개 fold로 나눠, 각 fold를 '나머지로 학습한 모델'로 채점한 원점수로
        /// 임계값을 산정하고, 최종 모델은 전체 표본으로 학습한다. 보정 표본 수 = 전체 표본 수.
        /// (고정 분할 시 보정 Run 수십 개의 우연한 분포에 임계값이 좌우되어 오탐률이 목표의 수 배로 흔들리는 문제를 줄인다)
        /// </summary>
        /// <param name="groupOf">같은 그룹(예: 같은 Run)의 표본은 같은 fold에 들어간다. null이면 Tag</param>
        public static StepAwareDetector FitCrossFitted(IEnumerable<RfSample> golden, string[] names, EnsembleOptions opt,
                                                       int folds = 5, int minSamplesPerFeature = 10, int? minCalibSamples = null,
                                                       Func<RfSample, string> groupOf = null, int seed = 20270101)
        {
            var all = golden.ToList();
            if (groupOf == null) groupOf = s => s.Tag ?? "";
            folds = Math.Max(2, folds);

            // 그룹 → fold (이름 정렬 후 고정 시드 셔플 → 재현 가능)
            var groups = all.Select(groupOf).Distinct().OrderBy(g => g, StringComparer.Ordinal).ToList();
            var rng = new Random(seed);
            for (int i = groups.Count - 1; i > 0; i--)
            {
                int j = rng.Next(i + 1);
                var t = groups[i]; groups[i] = groups[j]; groups[j] = t;
            }
            var foldOf = new Dictionary<string, int>();
            for (int i = 0; i < groups.Count; i++) foldOf[groups[i]] = i % folds;

            int p = names.Length;
            int minTrain = Math.Max(2 * (p + 1), minSamplesPerFeature * p);
            int minCalib = minCalibSamples ?? Math.Max(50, (int)Math.Ceiling(1.0 / opt.TargetFpr));

            EnsembleModel FitKey(string key, List<RfSample> set)
            {
                var oof = new List<Tuple<double, double, double>>(set.Count);
                for (int f = 0; f < folds; f++)
                {
                    var tr = set.Where(s => foldOf[groupOf(s)] != f).Select(s => s.Features).ToList();
                    var te = set.Where(s => foldOf[groupOf(s)] == f).Select(s => s.Features).ToList();
                    if (te.Count == 0) continue;
                    var mf = EnsembleModel.FitUncalibrated(key, names, tr, opt);
                    oof.AddRange(te.Select(mf.RawScores));
                }
                var m = EnsembleModel.FitUncalibrated(key, names, set.Select(s => s.Features).ToList(), opt);
                m.CalibrateRaw(oof);
                return m;
            }

            var det = new StepAwareDetector { FeatureNames = names };
            det.Global = FitKey("GLOBAL", all);
            foreach (var grp in all.GroupBy(s => KeyOf(s.Recipe, s.Step)))
            {
                var set = grp.ToList();
                int smallestTrain = set.Count - set.GroupBy(s => foldOf[groupOf(s)]).Max(g => g.Count());
                if (smallestTrain < minTrain || set.Count < minCalib) continue;   // → GLOBAL로 대체
                det.Models[grp.Key] = FitKey(grp.Key, set);
            }
            return det;
        }

        public EnsembleModel Resolve(RfSample s)
        {
            EnsembleModel m;
            return Models.TryGetValue(KeyOf(s.Recipe, s.Step), out m) ? m : Global;
        }

        public AnomalyResult Diagnose(RfSample s) => Resolve(s).Diagnose(s.Features);

        /// <summary>Step 모델별로 검증 세트에서 가중치 튜닝. 반환: key → (w, AUC)</summary>
        public Dictionary<string, Tuple<double, double>> TuneWeights(IEnumerable<RfSample> valid,
                                                                    IEnumerable<RfSample> calib)
        {
            var v = valid.ToList();
            var c = calib.ToList();
            var result = new Dictionary<string, Tuple<double, double>>();
            foreach (var kv in Models)
            {
                var vs = v.Where(s => KeyOf(s.Recipe, s.Step) == kv.Key).ToList();
                if (vs.Select(s => s.Label).Distinct().Count() < 2) continue;   // 정상·이상 모두 있어야 함
                var cal = c.Where(s => KeyOf(s.Recipe, s.Step) == kv.Key).Select(s => s.Features).ToList();
                double auc = kv.Value.TuneWeight(vs.Select(s => s.Features).ToList(),
                                                 vs.Select(s => s.Label).ToList(), cal);
                result[kv.Key] = Tuple.Create(kv.Value.WeightMahalanobis, auc);
            }
            return result;
        }

        public void SetMode(FusionMode mode)
        {
            foreach (var m in Models.Values) m.Mode = mode;
            if (Global != null) Global.Mode = mode;
        }

        /// <summary>모델 저장 (JSON + gzip). 운영 Iruza에서는 파일 교체만으로 모델 갱신</summary>
        public void Save(string path) => GzipJson.Write(path, this);

        public static StepAwareDetector Load(string path) => GzipJson.Read<StepAwareDetector>(path);
    }

    #endregion

    #region ───────── JSON(gzip) 저장 유틸 ─────────

    /// <summary>
    /// gzip 압축 JSON 저장/읽기. System.Text.Json 3.0(.NET Core 3.1 내장, NuGet 4.7.x)부터 있는
    /// 문자열 기반 API만 사용한다. (Stream 오버로드는 6.0, DefaultIgnoreCondition은 5.0부터라 쓰지 않음)
    /// </summary>
    internal static class GzipJson
    {
        private static readonly JsonSerializerOptions Options = new JsonSerializerOptions { MaxDepth = 128 };
        private static readonly UTF8Encoding Utf8NoBom = new UTF8Encoding(false);

        public static void Write<T>(string path, T value)
        {
            string json = JsonSerializer.Serialize(value, Options);
            using (var fs = File.Create(path))
            using (var gz = new GZipStream(fs, CompressionLevel.Optimal))
            using (var sw = new StreamWriter(gz, Utf8NoBom))
                sw.Write(json);
        }

        public static T Read<T>(string path)
        {
            string json;
            using (var fs = File.OpenRead(path))
            using (var gz = new GZipStream(fs, CompressionMode.Decompress))
            using (var sr = new StreamReader(gz, Encoding.UTF8))
                json = sr.ReadToEnd();
            return JsonSerializer.Deserialize<T>(json, Options);
        }
    }

    #endregion

    #region ───────── 6) 궤적 잔차 Feature (WP6 연계) ─────────

    /// <summary>
    /// Golden Run에서 target ≈ Σ c_k·(ref−ref₀)^k 를 강건(2회 절단) 최소제곱으로 학습하고, 잔차를 새 특성으로 쓴다.
    /// 예) x_ohm vs r_ohm (Smith Chart 궤적), s_ref vs load_pos, vvc2 vs apc_pressure 등.
    /// IF가 꼬리에서 놓치는 '정상 궤적 주변의 이탈'을 1차원 잔차로 펴서 직접 잡는다.
    /// EnsembleOptions.TrajectoryResiduals로 보조 검출기로 쓰거나, Augment로 특성에 붙여 Feature Store에 넣을 수 있다.
    /// </summary>
    public sealed class PolyResidualFeature
    {
        public string Name { get; set; }
        public int Target { get; set; }
        public int Reference { get; set; }
        public double RefCenter { get; set; }
        /// <summary>기준값 표준화 스케일(MAD) — 범위가 좁은 기준값에서도 다항식 적합이 안정되도록</summary>
        public double RefScale { get; set; } = 1.0;
        public double[] Coef { get; set; }
        /// <summary>Golden Run 잔차의 median / 전역 MAD</summary>
        public double ResidualMedian { get; set; }
        public double ResidualScale { get; set; }
        /// <summary>이분산 보정: |잔차| ≈ poly(ref) — 궤적 끝단처럼 잔차가 원래 큰 구간의 오탐을 줄인다</summary>
        public double[] ScaleCoef { get; set; }

        public double AbsZ(double[] x) => Math.Abs((Residual(x) - ResidualMedian) / LocalScale(x[Reference]));

        public double LocalScale(double reference)
        {
            if (ScaleCoef == null) return ResidualScale;
            double u = (reference - RefCenter) / RefScale, sd = Eval(ScaleCoef, u) / 0.7979;   // E|N(0,σ)| = 0.798σ
            return Math.Max(0.5 * ResidualScale, sd);                            // 하한: 전역 MAD의 절반
        }

        public static PolyResidualFeature Fit(IReadOnlyList<double[]> X, int target, int reference,
                                              int degree, string name)
        {
            var f = new PolyResidualFeature
            {
                Name = name,
                Target = target,
                Reference = reference,
                RefCenter = Stat.Median(X.Select(x => x[reference]).ToList())
            };
            var refCol = X.Select(x => x[reference]).ToList();
            double rs = Stat.Mad(refCol, f.RefCenter);
            if (rs < 1e-12) rs = Stat.StdDev(refCol);
            f.RefScale = rs < 1e-12 ? 1.0 : rs;
            var use = X.ToList();
            for (int pass = 0; pass < 3; pass++)
            {
                f.Coef = LeastSquares(use.Select(f.U).ToList(),
                                      use.Select(x => x[target]).ToList(), degree);
                if (pass == 2) break;
                var res = X.Select(f.Residual).ToList();
                double med = Stat.Median(res), mad = Math.Max(1e-12, Stat.Mad(res, med));
                use = X.Where((x, i) => Math.Abs(res[i] - med) <= 3 * mad).ToList();   // 오염 제외 후 재적합
            }
            var rAll = X.Select(f.Residual).ToList();
            f.ResidualMedian = Stat.Median(rAll);
            f.ResidualScale = Math.Max(1e-12, Stat.Mad(rAll, f.ResidualMedian));
            // 국소 스케일: 정상 표본(use)의 |잔차−중앙값|을 기준 특성의 다항식으로 근사
            f.ScaleCoef = LeastSquares(use.Select(f.U).ToList(),
                                       use.Select(x => Math.Abs(f.Residual(x) - f.ResidualMedian)).ToList(), degree);
            return f;
        }

        public double Residual(double[] x) => x[Target] - Eval(Coef, U(x));

        private double U(double[] x) => (x[Reference] - RefCenter) / RefScale;

        private static double Eval(double[] c, double u)
        {
            double v = 0, pw = 1;
            for (int k = 0; k < c.Length; k++) { v += c[k] * pw; pw *= u; }
            return v;
        }

        /// <summary>원 특성 뒤에 잔차 특성들을 붙인 새 벡터</summary>
        public static double[] Augment(double[] x, IList<PolyResidualFeature> feats)
        {
            var r = new double[x.Length + feats.Count];
            Array.Copy(x, r, x.Length);
            for (int i = 0; i < feats.Count; i++) r[x.Length + i] = feats[i].Residual(x);
            return r;
        }

        /// <summary>y ≈ Σ c_k·u^k 최소제곱</summary>
        private static double[] LeastSquares(IList<double> us, IList<double> ys, int degree)
        {
            int m = degree + 1;
            var A = new double[m, m + 1];                 // [ΦᵀΦ | Φᵀy]
            for (int i = 0; i < us.Count; i++)
            {
                var phi = new double[m];
                double pw = 1;
                for (int k = 0; k < m; k++) { phi[k] = pw; pw *= us[i]; }
                for (int a = 0; a < m; a++)
                {
                    for (int b = 0; b < m; b++) A[a, b] += phi[a] * phi[b];
                    A[a, m] += phi[a] * ys[i];
                }
            }
            // 부분 피벗 가우스 소거
            for (int c = 0; c < m; c++)
            {
                int piv = c;
                for (int r = c + 1; r < m; r++) if (Math.Abs(A[r, c]) > Math.Abs(A[piv, c])) piv = r;
                for (int k = 0; k <= m; k++) { double t = A[c, k]; A[c, k] = A[piv, k]; A[piv, k] = t; }
                for (int r = 0; r < m; r++)
                {
                    if (r == c || A[c, c] == 0) continue;
                    double fct = A[r, c] / A[c, c];
                    for (int k = c; k <= m; k++) A[r, k] -= fct * A[c, k];
                }
            }
            var coef = new double[m];
            for (int k = 0; k < m; k++) coef[k] = A[k, k] == 0 ? 0 : A[k, m] / A[k, k];
            return coef;
        }
    }

    #endregion
}
