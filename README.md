# Iruza – RF Smith Chart Analyzer
**H&iruja Inc.**  |  Plasma 장비 RF 임피던스 매칭 분석 솔루션

---

## 프로젝트 구조

```
Iruza/
├── Iruza.csproj                     WinForms 프로젝트 파일
├── src/
│   ├── Program.cs                   진입점 (STAThread)
│   ├── MainShell.cs                 3탭 메인 셸 폼
│   ├── Core/
│   │   └── SmithChartCalculator.cs  RF 핵심 계산 엔진
│   ├── Renderer/
│   │   └── SmithChartRenderer.cs    공용 System.Drawing 렌더러
│   ├── Fingerprint/
│   │   ├── FingerprintModel.cs      패턴 데이터 모델 (4가지)
│   │   └── PlasmaFingerprintPanel.cs 탭1 – Fingerprint 분석 UI
│   ├── Measurement/
│   │   ├── MeasurementStep.cs       측정 스텝 (15컬럼) 모델
│   │   ├── MeasurementDataset.cs    데이터셋 + CSV 입출력
│   │   └── MeasurementViewerPanel.cs 탭2 – 데이터 뷰어 UI
│   └── Matching/
│       └── ImpedanceMatchingPanel.cs 탭3 – 매칭 계산기 UI
├── sample/
│   └── sample_measurement.csv       샘플 CSV 파일
└── README.md
```

---

## 빌드 방법

### Visual Studio 2022 (권장)
1. `Iruza.csproj` 더블클릭 → 프로젝트 열기
2. `F5` 빌드 및 실행

### .NET CLI
```bash
dotnet build Iruza.csproj
dotnet run --project Iruza.csproj
```

> **요구사항**: .NET Framework 4.8 또는 .NET 6+ (WinForms)
> 추가 NuGet 패키지 없음 — `System.Drawing`, `System.Numerics` (BCL 기본 포함)

---

## 탭별 기능

### 탭 1 — Plasma Fingerprint 분석
- 4가지 패턴 카드: 정상 / Matching 이상 / Chamber Drift / Arc 발생 전조
- 스미스차트에 정상 궤적(실선) + 이상 궤적(점선) 오버레이
- 포인트 호버 시 Z, |Γ|, VSWR, RL 표시

### 탭 2 — 측정 데이터 뷰어
| 기능 | 설명 |
|------|------|
| CSV 가져오기 | 15컬럼 형식 자동 파싱 |
| CSV 내보내기 | 전체 계산값 포함 저장 |
| 그리드 편집 | 셀 수정 → 자동 재계산 |
| 색상 모드 | VSWR 열지도 / 단색 / 전력 그라데이션 |
| PNG 저장 | 1200×1200 고해상도 |

**15컬럼 CSV 형식**
```
Step, Vout (Vrms), Iout (Arms), Phase θ (deg), R (Ω), X (Ω),
Γ real, Γ imag, |Γ|, VSWR, Z text, z normalized,
Forward P (W), Reflected P (W), Delivered P (W)
```

### 탭 3 — 임피던스 매칭 계산기
| 계산 | 메서드 |
|------|--------|
| 직렬/병렬 L·C 소자 적용 | `ApplySeriesL/C`, `ApplyShuntL/C` |
| L-network 자동 설계 | `LNetworkMatch()` |
| λ/4 변환기 | `QuarterWaveTransformer()` |
| 단일 스텁 매칭 | `SingleStubMatch()` |

---

## 핵심 계산 공식

| 수식 | 내용 |
|------|------|
| `Γ = (Z-Z₀)/(Z+Z₀)` | 반사계수 |
| `VSWR = (1+|Γ|)/(1-|Γ|)` | 정재파비 |
| `RL = -20·log₁₀(|Γ|)` dB | 반사손실 |
| `Z = V/I·e^(jθ)` | V/I/θ → 임피던스 |
| `P_del = P_fwd·(1-|Γ|²)` | 전달전력 |

---

## 라이선스
© 2025 H&iruja Inc. All rights reserved.
