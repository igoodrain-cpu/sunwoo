using System.Globalization;
using System.Security.Cryptography;
using System.Text;
using MeasurementImporterService.Models;

namespace MeasurementImporterService.Services;

/// <summary>
/// 공정 CSV 파일을 읽어 PROCESS_RUN / PROCESS_STEP / SMITH_CHART_POINT 적재용 모델로 변환한다.
/// 헤더 유무와 관계없이 컬럼 순서 기반으로 파싱한다.
/// </summary>
public sealed class CsvParserService
{
    private const int ExpectedColumnCount = 43;

    // 임피던스 사양 범위 (Zin/Zp 공통)
    //   R(Resistance): 0 ~ 3000 Ω,  X(Reactance): -3000 ~ +3000 Ω
    private const double RMin = 0.0;
    private const double RMax = 3000.0;
    private const double XMin = -3000.0;
    private const double XMax = 3000.0;

    // R >= 0 이면 |Γ| <= 1 이 수학적으로 보장된다. R = 0(순수 리액턴스, RF Off 시 R=X=0 포함)이면
    // |Γ| = 1 이 정확한 값이므로 이는 이상치가 아니다. 1을 넘는 것은 부동소수점 오차뿐이므로
    // 상한은 1.0으로 둔다. (gamma_mag NUMERIC(9,6)은 1.000000 저장 가능)
    private const double GammaMagLimit = 1.0;

    // |Γ|가 이 값 이상이면 VSWR이 사실상 무한대(완전 반사)이므로 VswrLimit으로 저장한다.
    private const double GammaTotalReflection = 1.0 - 1e-6;
    private const decimal VswrLimit = 999.999m;

    // 상위 계측 시스템의 로깅 버그로 B채널 Vrms가 10^6배 부풀려져 들어오는 경우가 있다
    // (예: 실제 17.79V가 17794063.61로 기록됨). process_step.b_vrms(NUMERIC(10,3), 정수부
    // 최대 7자리)와 smith_chart_point.vout_vrms(NUMERIC(10,4), 정수부 최대 6자리) 양쪽에서
    // numeric overflow(22003)를 일으키므로, 파싱 시점에 스케일을 정규화한다.
    private const decimal VrmsAnomalyThreshold = 1_000_000m;
    private const decimal VrmsScaleFactor = 1_000_000m;

    public async Task<string> ComputeFileHashAsync(string filePath, CancellationToken cancellationToken)
    {
        var fileBytes = await File.ReadAllBytesAsync(filePath, cancellationToken);
        return ComputeSha256(fileBytes);
    }

    public async Task<MeasurementBatch> ParseAsync(
        string filePath,
        string? defaultRecipeName,
        string? defaultEquipmentId,
        CancellationToken cancellationToken)
    {
        var fileBytes = await File.ReadAllBytesAsync(filePath, cancellationToken);
        var fileHash = ComputeSha256(fileBytes);

        using var reader = new StreamReader(new MemoryStream(fileBytes), Encoding.UTF8, detectEncodingFromByteOrderMarks: true);

        var firstLine = await reader.ReadLineAsync(cancellationToken)
            ?? throw new InvalidDataException($"파일이 비어 있습니다: {filePath}");

        var firstColumns = SplitCsvLine(firstLine);
        ValidateColumnCount(firstColumns.Count, 1, filePath);

        var steps = new List<ProcessStepRecord>();
        int lineNumber = 1;

        if (LooksLikeDataRow(firstColumns))
        {
            try
            {
                steps.Add(MapRow(firstColumns));
            }
            catch (Exception ex)
            {
                throw new InvalidDataException(
                    $"1번째 줄 파싱 중 오류가 발생했습니다. 파일: {filePath}", ex);
            }
        }

        while (await reader.ReadLineAsync(cancellationToken) is { } line)
        {
            lineNumber++;

            if (string.IsNullOrWhiteSpace(line))
            {
                continue;
            }

            var columns = SplitCsvLine(line);
            ValidateColumnCount(columns.Count, lineNumber, filePath);

            if (!LooksLikeDataRow(columns))
            {
                continue;
            }

            try
            {
                steps.Add(MapRow(columns));
            }
            catch (Exception ex)
            {
                throw new InvalidDataException(
                    $"{lineNumber}번째 줄 파싱 중 오류가 발생했습니다. 파일: {filePath}", ex);
            }
        }

        if (steps.Count == 0)
        {
            throw new InvalidDataException($"파싱 가능한 데이터 행이 없습니다: {filePath}");
        }

        var startedAt = steps.Select(GetStepDateTime).Min();
        var endedAt = steps.Select(GetStepDateTime).Max();

        var baseName = Path.GetFileNameWithoutExtension(filePath);
        var runName = TrimToLength($"{baseName}_{startedAt:yyyyMMddHHmmssfff}", 100)!;

        return new MeasurementBatch
        {
            BatchId = Guid.NewGuid(),
            SourceFile = Path.GetFileName(filePath),
            FileHash = fileHash,
            RunName = runName,
            RecipeName = baseName,
            EquipmentId = NullIfEmpty(defaultEquipmentId),
            StartedAt = startedAt,
            EndedAt = endedAt,
            Steps = steps
        };
    }

    private static void ValidateColumnCount(int actualCount, int lineNumber, string filePath)
    {
        if (actualCount != ExpectedColumnCount)
        {
            throw new InvalidDataException(
                $"{lineNumber}번째 줄의 컬럼 개수가 맞지 않습니다 (예상 {ExpectedColumnCount}, 실제 {actualCount}). 파일: {filePath}");
        }
    }

    private static bool LooksLikeDataRow(IReadOnlyList<string> columns)
    {
        if (columns.Count != ExpectedColumnCount)
        {
            return false;
        }

        return TryParseDate(columns[0], out _) &&
               TryParseTime(columns[1], out _) &&
               short.TryParse(columns[2], NumberStyles.Integer, CultureInfo.InvariantCulture, out _);
    }

    private static ProcessStepRecord MapRow(IReadOnlyList<string> c)
    {
        var logDate = ParseDate(c[0]);
        var logTime = ParseTime(c[1]);

        // 상위 시스템의 스케일 버그(10^6배 부풀려짐)를 여기서 한 번만 보정하고,
        // process_step과 smith_chart_point 양쪽에서 같은 보정값을 재사용한다.
        var sVrmsCorrected = CorrectVrmsScale(ParseDecimalOrNull(c[7]), "S.Mat.Vrms");
        var bVrmsCorrected = CorrectVrmsScale(ParseDecimalOrNull(c[18]), "B.Mat.Vrms");

         // 임피던스 컬럼 (사양 순서)
        //   c[34] S_Zin_R, c[35] S_Zin_X, c[36] B_Zin_R, c[37] B_Zin_X
        //   c[38] S_Zp_R,  c[39] S_Zp_X,  c[40] B_Zp_R,  c[41] B_Zp_X
            var sourcePoint = BuildSmithChartPoint(
            c, RfChannel.Source,
            voutVrms: sVrmsCorrected, ioutIdx: 8, phaseIdx: 9,
            rIdx: 34, xIdx: 35,
            forwardIdx: 5, reflectedIdx: 6, deliveredIdx: 10);

        var biasPoint = BuildSmithChartPoint(
            c, RfChannel.Bias,
            voutVrms: bVrmsCorrected, ioutIdx: 19, phaseIdx: 20,
            rIdx: 38, xIdx: 39,
            forwardIdx: 16, reflectedIdx: 17, deliveredIdx: 21);

        var sourcePoint_out = BuildSmithChartPoint(
            c, RfChannel.Source_Out,
            voutVrms: sVrmsCorrected, ioutIdx: 8, phaseIdx: 9,
            rIdx: 36, xIdx: 37,
            forwardIdx: 5, reflectedIdx: 6, deliveredIdx: 10);

        var biasPoint_out = BuildSmithChartPoint(
            c, RfChannel.Bias_Out,
            voutVrms: bVrmsCorrected, ioutIdx: 19, phaseIdx: 20,
            rIdx: 40, xIdx: 41,
            forwardIdx: 16, reflectedIdx: 17, deliveredIdx: 21);

        return new ProcessStepRecord
        {
            StepNum = short.Parse(c[2], CultureInfo.InvariantCulture),
            StepName = RequiredText(c[3], "StepName", 20),
            LogDate = logDate,
            LogTime = logTime,
            SrfFreq = ParseDecimalOrNull(c[4]),
            SFwd = ParseDecimalOrNull(c[5]),
            SRef = ParseDecimalOrNull(c[6]),
            SVrms = sVrmsCorrected,
            SIrms = ParseDecimalOrNull(c[8]),
            SPhase = ParseDecimalOrNull(c[9]),
            SDeliveredPwr = ParseDecimalOrNull(c[10]),
            SPresetLoad = ParseDecimalOrNull(c[11]),
            SPresetTune = ParseDecimalOrNull(c[12]),
            SLoadPos = ParseDecimalOrNull(c[13]),
            STunePos = ParseDecimalOrNull(c[14]),
            BrFreq = ParseDecimalOrNull(c[15]),
            BFwd = ParseDecimalOrNull(c[16]),
            BRef = ParseDecimalOrNull(c[17]),
            BVrms = bVrmsCorrected,
            BIrms = ParseDecimalOrNull(c[19]),
            BPhase = ParseDecimalOrNull(c[20]),
            BDeliveredPwr = ParseDecimalOrNull(c[21]),
            BPresetLoad = ParseDecimalOrNull(c[22]),
            BPresetTune = ParseDecimalOrNull(c[23]),
            BLoadPos = ParseDecimalOrNull(c[24]),
            BTunePos = ParseDecimalOrNull(c[25]),
            Vdc = ParseDecimalOrNull(c[26]),    
            ArFlow = ParseDecimalOrNull(c[27]),
            O2Flow = ParseDecimalOrNull(c[28]),
            ApcPressure = ParseDecimalOrNull(c[29]),
            ApcPosition = ParseDecimalOrNull(c[30]),
            Vvc1 = ParseDecimalOrNull(c[31]),
            Vvc2 = ParseDecimalOrNull(c[32]),
            Vvc3 = ParseDecimalOrNull(c[33]),
            ProcStatus = short.Parse(c[42], CultureInfo.InvariantCulture),
            SourcePoint = sourcePoint,
            BiasPoint = biasPoint,
            SourcePointOut = sourcePoint_out,
            BiasPointOut = biasPoint_out    
        };
    }

    /// <summary>
    /// Source/Bias 공통 Smith chart point 계산. R/X는 CSV 원본값을 그대로 사용하고,
    /// 여기서 계산되는 감마(Γ)와 VSWR은 DB numeric 컬럼 한계를 넘지 않도록 클램프한다.
    /// </summary>
    private static SmithChartPointRecord BuildSmithChartPoint(
        IReadOnlyList<string> c,
        RfChannel channel,
        decimal? voutVrms, int ioutIdx, int phaseIdx,
        int rIdx, int xIdx,
        int forwardIdx, int reflectedIdx, int deliveredIdx)
    {
        var forwardPower = ParseDecimalOrNull(c[forwardIdx]);
        var reflectedPower = ParseDecimalOrNull(c[reflectedIdx]);
        var deliveredPower = ParseDecimalOrNull(c[deliveredIdx]);

        const double z0 = 50.0;

        // 1) 사양 범위 검증: 범위를 벗어난 원본값(예: R = -0.01 같은 계측 노이즈)만 경고 후 클램프.
        //    R < 0 이 들어오면 |Γ| > 1 이 되므로, 감마 계산 전에 여기서 막는다.
        double r = ClampToSpec(ParseRequiredDouble(c[rIdx], channel, "R"), RMin, RMax, channel, "R");
        double x = ClampToSpec(ParseRequiredDouble(c[xIdx], channel, "X"), XMin, XMax, channel, "X");

        //double r = ParseRequiredDouble(c[rIdx], channel, "R");
        //double x = ParseRequiredDouble(c[xIdx], channel, "X");

        // 2) 반사계수 계산
        double gammaReal = CalcGammaReal(r, x, z0);
        double gammaImag = CalcGammaImag(r, x, z0);
        double gammaMag = CalcGammaMag(gammaReal, gammaImag);

        // 3) R >= 0 이 보장된 상태에서 |Γ| > 1 은 부동소수점 오차(1e-16 수준)뿐이므로 경고 없이 보정
        if (gammaMag > GammaMagLimit)
        {
            double scale = GammaMagLimit / gammaMag;
            gammaReal *= scale;
            gammaImag *= scale;
            gammaMag = GammaMagLimit;
        }

        // 4) VSWR: |Γ| ≈ 1(R ≈ 0, 순수 리액턴스 또는 RF Off)은 완전 반사 → 무한대이므로 상한값으로 저장.
        //    사양 범위 내 정상 데이터이므로 경고를 남기지 않는다.
        decimal vswr = gammaMag >= GammaTotalReflection
            ? VswrLimit
            : Math.Min(Convert.ToDecimal(CalcVSWR(gammaMag)), VswrLimit);

        string zText = CalcZText(r, x);
        string zNormalized = CalcZNormalized(r, x, z0);

        return new SmithChartPointRecord
        {
            Channel = channel,
            VoutVrms = voutVrms,
            IoutArms = ParseDecimalOrNull(c[ioutIdx]),
            PhaseDeg = ParseDecimalOrNull(c[phaseIdx]),

            ROhm = Convert.ToDecimal(r),
            XOhm = Convert.ToDecimal(x),
            GammaReal = Convert.ToDecimal(gammaReal),
            GammaImag = Convert.ToDecimal(gammaImag),
            GammaMag = Convert.ToDecimal(gammaMag),
            Vswr = vswr,

            ZText = zText,
            ZNormalized = zNormalized,

            ForwardPowerW = forwardPower,
            ReflectedPowerW = reflectedPower,
            DeliveredPowerW = deliveredPower,
            ReturnLossDb = ComputeReturnLossDb(Convert.ToDecimal(gammaMag), forwardPower, reflectedPower),
            EfficiencyPct = ComputeEfficiencyPct(forwardPower, deliveredPower)
        };
    }

    /// <summary>
    /// 상위 계측 시스템의 로깅 버그로 Vrms가 10^6배 부풀려져 들어오는 경우를 감지해 보정한다.
    /// 정상적인 RF 매칭 네트워크 Vrms는 이 임계값보다 훨씬 작으므로, 이 범위를 넘으면
    /// 스케일 오류로 간주해 10^6으로 나눈다. 그렇지 않으면 process_step.b_vrms
    /// (NUMERIC(10,3)) / smith_chart_point.vout_vrms(NUMERIC(10,4))에서 numeric overflow가 난다.
    /// </summary>
    private static decimal? CorrectVrmsScale(decimal? raw, string fieldName)
    {
        if (!raw.HasValue)
        {
            return raw;
        }

        var abs = Math.Abs(raw.Value);
        if (abs < VrmsAnomalyThreshold)
        {
            return raw;
        }

        var corrected = raw.Value / VrmsScaleFactor;
        Console.Error.WriteLine(
            $"[CsvParserService] 경고: {fieldName} 값({raw.Value:G10})이 비정상적으로 커서 " +
            $"10^6 스케일 오류로 간주하고 {corrected:G10}(으)로 보정했습니다. 원본 계측 시스템의 " +
            $"단위/스케일 버그일 가능성이 있으니 상위 시스템 쪽도 확인이 필요합니다.");

        return corrected;
    }

    /// <summary>
    /// 임피던스 원본값을 사양 범위로 제한한다. 범위를 벗어난 경우에만 경고를 남긴다.
    /// 프로젝트에 ILogger가 주입 가능하면 Console.Error 대신 그쪽으로 교체 권장.
    /// </summary>
    private static double ClampToSpec(double value, double min, double max, RfChannel channel, string field)
    {
        if (value >= min && value <= max)
        {
            return value;
        }

        double clamped = Math.Clamp(value, min, max);
        Console.Error.WriteLine(
            $"[CsvParserService] 경고: {channel} 채널 {field}={value:G6} 이(가) 사양 범위({min:G6} ~ {max:G6})를 " +
            $"벗어나 {clamped:G6}(으)로 보정했습니다.");
        return clamped;
    }

    private static double ParseRequiredDouble(string value, RfChannel channel, string field)
    {
        if (double.TryParse(value?.Trim(), NumberStyles.Float, CultureInfo.InvariantCulture, out var result)
            && double.IsFinite(result))
        {
            return result;
        }

        throw new FormatException($"{channel} 채널 {field} 값이 숫자가 아닙니다: '{value}'");
    }

    private static decimal? ComputeReturnLossDb(decimal? gammaMag, decimal? forwardPower, decimal? reflectedPower)
    {
        var ratio = gammaMag;

        if (!ratio.HasValue && forwardPower.HasValue && reflectedPower.HasValue && forwardPower.Value > 0 && reflectedPower.Value >= 0)
        {
            ratio = (decimal)Math.Sqrt((double)(reflectedPower.Value / forwardPower.Value));
        }

        if (!ratio.HasValue || ratio.Value <= 0)
        {
            // |Γ| = 0 (완전 정합) → Return Loss 무한대이므로 null
            return null;
        }
        if (ratio.Value >= 1)
        {
            // |Γ| = 1 (완전 반사) → Return Loss = 0 dB
            return 0m;
        }

        return decimal.Round((decimal)(-20d * Math.Log10((double)ratio.Value)), 2);
    }

    private static decimal? ComputeEfficiencyPct(decimal? forwardPower, decimal? deliveredPower)
    {
        if (!forwardPower.HasValue || !deliveredPower.HasValue || forwardPower.Value <= 0)
        {
            return null;
        }

        return decimal.Round(deliveredPower.Value / forwardPower.Value * 100m, 2);
    }

    private static DateTime GetStepDateTime(ProcessStepRecord step) =>
        step.LogDate.ToDateTime(step.LogTime);

    private static DateOnly ParseDate(string value)
    {
        if (TryParseDate(value, out var date))
        {
            return date;
        }

        throw new FormatException($"날짜 형식이 올바르지 않습니다: {value}");
    }

    private static bool TryParseDate(string value, out DateOnly date)
    {
        string[] formats = ["yyyy/MM/dd", "yyyy-MM-dd", "yyyyMMdd"];
        return DateOnly.TryParseExact(value.Trim(), formats, CultureInfo.InvariantCulture, DateTimeStyles.None, out date);
    }

    private static TimeOnly ParseTime(string value)
    {
        if (TryParseTime(value, out var time))
        {
            return time;
        }

        throw new FormatException($"시간 형식이 올바르지 않습니다: {value}");
    }

    private static bool TryParseTime(string value, out TimeOnly time)
    {
        string[] formats = ["HH:mm:ss:fff", "HH:mm:ss.fff", "HH:mm:ss", "H:mm:ss", "H:mm:ss:fff", "H:mm:ss.fff"];
        return TimeOnly.TryParseExact(value.Trim(), formats, CultureInfo.InvariantCulture, DateTimeStyles.None, out time);
    }

    private static decimal? ParseDecimalOrNull(string value)
    {
        if (string.IsNullOrWhiteSpace(value))
        {
            return null;
        }

        return decimal.Parse(value.Trim(), NumberStyles.Float | NumberStyles.AllowLeadingSign, CultureInfo.InvariantCulture);
    }

    private static string RequiredText(string value, string columnName, int? maxLength = null)
    {
        var text = NullIfEmpty(value);
        return text is null
            ? throw new FormatException($"{columnName} 값이 비어 있습니다.")
            : TrimToLength(text, maxLength)!;
    }

    private static string? NullIfEmpty(string value) =>
        string.IsNullOrWhiteSpace(value) ? null : value.Trim();

    private static string? TrimToLength(string? value, int? maxLength)
    {
        if (value is null || maxLength is null || value.Length <= maxLength.Value)
        {
            return value;
        }

        return value[..maxLength.Value];
    }

    /// <summary>
    /// 큰따옴표로 감싸진 필드 안의 콤마를 보존하는 간단한 CSV 라인 분리기.
    /// </summary>
    private static List<string> SplitCsvLine(string line)
    {
        var result = new List<string>();
        var current = new StringBuilder();
        bool inQuotes = false;

        for (int i = 0; i < line.Length; i++)
        {
            char ch = line[i];

            if (inQuotes)
            {
                if (ch == '"')
                {
                    if (i + 1 < line.Length && line[i + 1] == '"')
                    {
                        current.Append('"');
                        i++;
                    }
                    else
                    {
                        inQuotes = false;
                    }
                }
                else
                {
                    current.Append(ch);
                }
            }
            else
            {
                if (ch == '"')
                {
                    inQuotes = true;
                }
                else if (ch == ',')
                {
                    result.Add(current.ToString());
                    current.Clear();
                }
                else
                {
                    current.Append(ch);
                }
            }
        }

        result.Add(current.ToString());
        return result;
    }

    private static string ComputeSha256(byte[] data)
    {
        var hash = SHA256.HashData(data);
        return Convert.ToHexString(hash);
    }

    /// <summary>
    /// V(rms), I(rms), 위상각(deg)으로부터 임피던스의 실수부(R)를 계산합니다.
    /// Z = (V/I) * (cosθ + j sinθ)  →  R = (V/I) * cosθ
    /// </summary>
    /// <param name="vrms">전압 실효값 (V)</param>
    /// <param name="irms">전류 실효값 (A)</param>
    /// <param name="phaseDeg">전압-전류 위상차 (degree)</param>
    public static double CalcR(double vrms, double irms, double phaseDeg)
    {
        if (irms == 0) return 0d;

        double magnitude = vrms / irms;
        double phaseRad = phaseDeg * Math.PI / 180.0;

        return magnitude * Math.Cos(phaseRad);
    }

    /// <summary>
    /// V(rms), I(rms), 위상각(deg)으로부터 임피던스의 허수부(X)를 계산합니다.
    /// Z = (V/I) * (cosθ + j sinθ)  →  X = (V/I) * sinθ
    /// </summary>
    /// <param name="vrms">전압 실효값 (V)</param>
    /// <param name="irms">전류 실효값 (A)</param>
    /// <param name="phaseDeg">전압-전류 위상차 (degree)</param>
    public static double CalcX(double vrms, double irms, double phaseDeg)
    {
        if (irms == 0) return 0d;

        double magnitude = vrms / irms;
        double phaseRad = phaseDeg * Math.PI / 180.0;

        return magnitude * Math.Sin(phaseRad);
    }

    /// <summary>
    /// 임피던스(R, X)와 기준 임피던스(Z0)로부터 반사계수의 실수부(Γreal)를 계산합니다.
    /// Γ = (Z - Z0) / (Z + Z0),  Z = R + jX
    /// </summary>
    /// <param name="r">임피던스 실수부 R (Ω)</param>
    /// <param name="x">임피던스 허수부 X (Ω)</param>
    /// <param name="z0">기준 임피던스 (보통 50Ω)</param>
    public static double CalcGammaReal(double r, double x, double z0)
    {
        // 분자: (R - Z0) + jX
        double numReal = r - z0;
        double numImag = x;

        // 분모: (R + Z0) + jX
        double denReal = r + z0;
        double denImag = x;

        double denomSq = denReal * denReal + denImag * denImag;
        if (denomSq == 0) return 0d;

        // 복소수 나눗셈: (a+jb)/(c+jd) = [(ac+bd) + j(bc-ad)] / (c²+d²)
        return (numReal * denReal + numImag * denImag) / denomSq;
    }

    /// <summary>
    /// 임피던스(R, X)와 기준 임피던스(Z0)로부터 반사계수의 허수부(Γimag)를 계산합니다.
    /// Γ = (Z - Z0) / (Z + Z0),  Z = R + jX
    /// </summary>
    /// <param name="r">임피던스 실수부 R (Ω)</param>
    /// <param name="x">임피던스 허수부 X (Ω)</param>
    /// <param name="z0">기준 임피던스 (보통 50Ω)</param>
    public static double CalcGammaImag(double r, double x, double z0)
    {
        double numReal = r - z0;
        double numImag = x;

        double denReal = r + z0;
        double denImag = x;

        double denomSq = denReal * denReal + denImag * denImag;
        if (denomSq == 0) return 0d;

        return (numImag * denReal - numReal * denImag) / denomSq;
    }

    /// <summary>
    /// 반사계수의 실수부/허수부로부터 크기 |Γ|를 계산합니다.
    /// |Γ| = sqrt(Γreal² + Γimag²)
    /// </summary>
    /// <param name="gammaReal">반사계수 실수부</param>
    /// <param name="gammaImag">반사계수 허수부</param>
    public static double CalcGammaMag(double gammaReal, double gammaImag)
    {
        return Math.Sqrt(gammaReal * gammaReal + gammaImag * gammaImag);
    }

    /// <summary>
    /// 반사계수 크기(|Γ|)로부터 VSWR을 계산합니다.
    /// VSWR = (1 + |Γ|) / (1 - |Γ|)
    /// </summary>
    /// <param name="gammaMag">반사계수 크기 (0~1)</param>
    public static double CalcVSWR(double gammaMag)
    {
        // |Γ| = 1이면 완전 반사(분모 0) → VSWR 발산 방지용 클램프
        const double epsilon = 1e-6;
        double clamped = Math.Min(gammaMag, 1 - epsilon);

        return (1 + clamped) / (1 - clamped);
    }

    /// <summary>
    /// 임피던스 R, X로부터 사람이 읽기 좋은 형태의 Z 텍스트를 생성합니다.
    /// 예: R=75.20, X=-50.30 → "75.20 - j50.30 Ω"
    /// </summary>
    /// <param name="r">임피던스 실수부 R (Ω)</param>
    /// <param name="x">임피던스 허수부 X (Ω)</param>
    public static string CalcZText(double r, double x)
    {
        string sign = x >= 0 ? "+" : "-";
        return $"{r:F2} {sign} j{Math.Abs(x):F2} Ω";
    }

    /// <summary>
    /// 임피던스 R, X를 기준 임피던스 Z0로 정규화한 텍스트를 생성합니다.
    /// z = Z / Z0 = (R/Z0) + j(X/Z0)
    /// 예: R=75.20, X=-50.30, Z0=50 → "1.504 - j1.006"
    /// </summary>
    /// <param name="r">임피던스 실수부 R (Ω)</param>
    /// <param name="x">임피던스 허수부 X (Ω)</param>
    /// <param name="z0">기준 임피던스 (보통 50Ω)</param>
    public static string CalcZNormalized(double r, double x, double z0)
    {
        if (z0 == 0) return string.Empty;

        double zr = r / z0;
        double zx = x / z0;
        string sign = zx >= 0 ? "+" : "-";

        return $"{zr:F3} {sign} j{Math.Abs(zx):F3}";
    }
}
