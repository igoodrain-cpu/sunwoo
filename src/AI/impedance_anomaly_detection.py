# -*- coding: utf-8 -*-
"""
impedance_anomaly_detection.py
--------------------------------
스미스 차트 임피던스 궤적(Step 1~N)에서 정상/비정상 스텝을 탐지하는 프로토타입.

입력 데이터 형태 (Iruza CSV 컬럼과 동일):
    Vout_Vrms, Iout_Arms, theta_deg, R, X, Gamma_real, Gamma_imag, VSWR, Fwd_W, Ref_W

탐지 방법 4가지를 앙상블로 결합:
    A. 스텝 델타 Z-score (규칙 기반, 즉시 적용)
    B. Robust Mahalanobis Distance (기준 분포 대비 이상치)
    C. Isolation Forest (다변량 비지도 이상탐지)
    D. CUSUM 변화점 탐지 (궤적 중간의 급격한 패턴 변화)

각 방법은 0~1 스코어로 정규화 후 가중 평균하여 최종 anomaly_score를 산출하고,
threshold를 넘으면 label = 'ABNORMAL' 로 표시한다.

C#/.NET(Iruza WinForms)로 이식할 때는:
    - A, D는 순수 수학 연산이라 C#으로 그대로 포팅 가능 (외부 라이브러리 불필요)
    - B(Mahalanobis)도 공분산 역행렬만 있으면 C#에서 계산 가능 (Math.NET Numerics 사용)
    - C(IsolationForest)는 Python으로 학습 후 ONNX로 export하여 C#(ONNX Runtime)에서 추론하거나,
      ML.NET의 RandomizedPcaTrainer / Anomaly Detection API로 대체 가능
"""

import numpy as np
import pandas as pd
from sklearn.covariance import EllipticEnvelope
from sklearn.ensemble import IsolationForest
from sklearn.preprocessing import StandardScaler
import matplotlib.pyplot as plt

# =========================================================
# 0. 샘플 데이터 생성 (실제로는 CSV에서 로드)
#    스크린샷의 Bias 데이터 패턴을 흉내내어 Step 7~8 근처에 이상치를 주입
# =========================================================
def load_sample_data():
    np.random.seed(0)
    n = 10
    # 정상 궤적: R, X가 점진적으로 수렴
    R = np.array([20.7, 22.9, 22.6, 24.9, 26.5, 26.1, 12.8, 27.4, 18.2, 0.0])
    X = np.array([0.39, -0.48, 0.78, 0.35, 0.86, -1.72, 0.11, 0.29, 0.21, 0.0])
    Vout = np.array([5.39, 25.24, 23.01, 26.63, 26.40, 25.66, 0.51, 4.39, 4.55, 0.0])
    Iout = np.array([0.26, 1.10, 1.02, 1.07, 0.99, 0.98, 0.04, 0.16, 0.25, 0.01])
    VSWR = np.array([2.412, 2.180, 2.218, 2.009, 1.888, 1.917, 3.922, 1.823, 2.747, 999.0])

    df = pd.DataFrame({
        "step": np.arange(1, n + 1),
        "R": R, "X": X, "Vout": Vout, "Iout": Iout, "VSWR": VSWR
    })
    # 마지막 스텝(측정 종료/0점)은 별도 처리 대상이므로 제외
    df = df[df["Vout"] > 0.1].reset_index(drop=True)
    return df


# =========================================================
# A. 스텝 델타 Z-score (1차 방법: 인접 스텝 간 급변 탐지)
# =========================================================
def method_a_step_delta_zscore(df):
    gamma = df["R"] + 1j * df["X"]  # 간이 Γ 근사 (정확히는 (Z-Z0)/(Z+Z0) 정규화 필요)
    delta = np.abs(np.diff(gamma, prepend=gamma.iloc[0] if hasattr(gamma, "iloc") else gamma[0]))
    mu, sigma = np.mean(delta), np.std(delta) + 1e-9
    z = (delta - mu) / sigma
    score = np.clip(z / 3.0, 0, 1)  # 3-sigma 기준 정규화
    return score


# =========================================================
# B. Robust Mahalanobis Distance (기준 분포 대비 이상치)
# =========================================================
def method_b_mahalanobis(df, feature_cols=("R", "X")):
    X_feat = df[list(feature_cols)].values
    try:
        ee = EllipticEnvelope(contamination=0.2, random_state=0).fit(X_feat)
        dist = ee.mahalanobis(X_feat)
    except Exception:
        # 샘플 수가 적을 때(<특징수+1) fallback: 표준 마할라노비스
        cov = np.cov(X_feat.T) + np.eye(X_feat.shape[1]) * 1e-6
        inv_cov = np.linalg.inv(cov)
        mean = X_feat.mean(axis=0)
        diff = X_feat - mean
        dist = np.einsum("ij,jk,ik->i", diff, inv_cov, diff)
    score = (dist - dist.min()) / (dist.max() - dist.min() + 1e-9)
    return score


# =========================================================
# C. Isolation Forest (다변량 비지도 이상탐지)
# =========================================================
def method_c_isolation_forest(df, feature_cols=("R", "X", "Vout", "Iout", "VSWR")):
    X_feat = StandardScaler().fit_transform(df[list(feature_cols)].values)
    clf = IsolationForest(n_estimators=200, contamination=0.2, random_state=0)
    clf.fit(X_feat)
    raw = -clf.score_samples(X_feat)  # 값이 클수록 이상치
    score = (raw - raw.min()) / (raw.max() - raw.min() + 1e-9)
    return score


# =========================================================
# D. CUSUM 변화점 탐지 (궤적 중간의 급격한 레벨 변화)
# =========================================================
def method_d_cusum(df, col="VSWR", k=0.5, h=4.0):
    x = df[col].values.astype(float)
    mu = np.mean(x)
    std = np.std(x) + 1e-9
    z = (x - mu) / std
    pos, neg = np.zeros(len(z)), np.zeros(len(z))
    for i in range(1, len(z)):
        pos[i] = max(0, pos[i - 1] + z[i] - k)
        neg[i] = min(0, neg[i - 1] + z[i] + k)
    cusum = np.maximum(pos, -neg)
    score = np.clip(cusum / h, 0, 1)
    return score


# =========================================================
# 앙상블: 4개 방법의 가중 평균 → 최종 이상 스코어 / 라벨
# =========================================================
def detect_anomalies(df, weights=(0.25, 0.25, 0.30, 0.20), threshold=0.5):
    sa = method_a_step_delta_zscore(df)
    sb = method_b_mahalanobis(df)
    sc = method_c_isolation_forest(df)
    sd = method_d_cusum(df)

    w = np.array(weights)
    w = w / w.sum()
    final_score = w[0] * sa + w[1] * sb + w[2] * sc + w[3] * sd

    df = df.copy()
    df["score_delta"] = sa
    df["score_mahal"] = sb
    df["score_iforest"] = sc
    df["score_cusum"] = sd
    df["anomaly_score"] = final_score
    df["label"] = np.where(final_score >= threshold, "ABNORMAL", "NORMAL")
    return df


# =========================================================
# 시각화: 스미스 차트풍 산점도에 정상(초록)/비정상(빨강) 표시
# =========================================================
def plot_result(df):
    fig, ax = plt.subplots(figsize=(6, 6))
    theta = np.linspace(0, 2 * np.pi, 200)
    ax.plot(np.cos(theta), np.sin(theta), color="gray", lw=1)  # |Γ|=1 외곽원 (근사 표시용)

    colors = df["label"].map({"NORMAL": "green", "ABNORMAL": "red"})
    # 간이 정규화: Γ ≈ (Z-50)/(Z+50), Z0=50Ω 가정
    Z = df["R"].values + 1j * df["X"].values
    gamma = (Z - 50) / (Z + 50)
    gr, gi = np.real(gamma), np.imag(gamma)

    ax.scatter(gr, gi, c=colors, s=120, edgecolors="k", zorder=3)
    for i, row in df.iterrows():
        ax.annotate(f"S{int(row['step'])}", (gr[i], gi[i]),
                    textcoords="offset points", xytext=(6, 6))
    ax.plot(gr, gi, color="lightgray", lw=1, zorder=1)  # 궤적 연결선

    ax.set_xlim(-1.1, 1.1); ax.set_ylim(-1.1, 1.1)
    ax.axhline(0, color="lightgray", lw=0.5); ax.axvline(0, color="lightgray", lw=0.5)
    ax.set_title("Impedance Trajectory: Normal(green) vs Abnormal(red)")
    ax.set_aspect("equal")
    plt.tight_layout()
    plt.savefig("/mnt/user-data/outputs/smith_anomaly_result.png", dpi=150)
    print("차트 저장: /mnt/user-data/outputs/smith_anomaly_result.png")


if __name__ == "__main__":
    df = load_sample_data()
    result = detect_anomalies(df)
    print(result[["step", "R", "X", "VSWR", "anomaly_score", "label"]].to_string(index=False))
    plot_result(result)
