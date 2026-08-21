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
    private const int ExpectedColumnCount = 34;

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
            RecipeName = NullIfEmpty(defaultRecipeName),
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
        var sourcePoint = ParseSmithChartPointS(c, RfChannel.Source);
        var biasPoint = ParseSmithChartPointB(c, RfChannel.Bias);

        return new ProcessStepRecord
        {
            StepNum = short.Parse(c[2], CultureInfo.InvariantCulture),
            StepName = RequiredText(c[3], "StepName", 20),
            LogDate = logDate,
            LogTime = logTime,
            SrfFreq = ParseDecimalOrNull(c[4]),
            SFwd = ParseDecimalOrNull(c[5]),
            SRef = ParseDecimalOrNull(c[6]),
            SVrms = ParseDecimalOrNull(c[7]),
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
            BVrms = ParseDecimalOrNull(c[18]),
            BIrms = ParseDecimalOrNull(c[19]),
            BPhase = ParseDecimalOrNull(c[20]),
            BDeliveredPwr = ParseDecimalOrNull(c[21]),
            BPresetLoad = ParseDecimalOrNull(c[22]),
            BPresetTune = ParseDecimalOrNull(c[23]),
            BLoadPos = ParseDecimalOrNull(c[24]),
            BTunePos = ParseDecimalOrNull(c[25]),
            ArFlow = ParseDecimalOrNull(c[26]),
            O2Flow = ParseDecimalOrNull(c[27]),
            ApcPressure = ParseDecimalOrNull(c[28]),
            ApcPosition = ParseDecimalOrNull(c[29]),
            Vvc1 = ParseDecimalOrNull(c[30]),
            Vvc2 = ParseDecimalOrNull(c[31]),
            Vvc3 = ParseDecimalOrNull(c[32]),
            ProcStatus = short.Parse(c[33], CultureInfo.InvariantCulture),
            SourcePoint = sourcePoint,
            BiasPoint = biasPoint
        };
    }

    private static SmithChartPointRecord ParseSmithChartPointS(IReadOnlyList<string> c, RfChannel channel)
    {

        //var gammaMag = ParseDecimalOrNull(c[startIndex + 7]);
        var forwardPower = ParseDecimalOrNull(c[5]);
        var reflectedPower = ParseDecimalOrNull(c[6]);
        var deliveredPower = ParseDecimalOrNull(c[10]);

        double z0 = 50.0;
        double r = CalcR(vrms: Convert.ToDouble(ParseDecimalOrNull(c[7]) ?? 0m),irms: Convert.ToDouble(ParseDecimalOrNull(c[8]) ?? 0m),phaseDeg: Convert.ToDouble(ParseDecimalOrNull(c[9]) ?? 0m));
        double x = CalcX(vrms: Convert.ToDouble(ParseDecimalOrNull(c[7]) ?? 0m), irms: Convert.ToDouble(ParseDecimalOrNull(c[8]) ?? 0m), phaseDeg: Convert.ToDouble(ParseDecimalOrNull(c[9]) ?? 0m));
        double gammaReal = CalcGammaReal(r, x, z0);
        double gammaImag = CalcGammaImag(r, x, z0);
        double gammaMag = CalcGammaMag(gammaReal, gammaImag);
        double vswr = CalcVSWR(gammaMag);

        string zText = CalcZText(r, x);
        string zNormalized = CalcZNormalized(r, x, z0);

        return new SmithChartPointRecord
        {
            Channel = channel,
            VoutVrms = ParseDecimalOrNull(c[7]),
            IoutArms = ParseDecimalOrNull(c[8]),
            PhaseDeg = ParseDecimalOrNull(c[9]),

           // ROhm = ParseDecimalOrNull(c[startIndex + 3]),
           // XOhm = ParseDecimalOrNull(c[startIndex + 4]),
           // GammaReal = ParseDecimalOrNull(c[startIndex + 5]),
           // GammaImag = ParseDecimalOrNull(c[startIndex + 6]),
           // GammaMag = gammaMag,
           // Vswr = ParseDecimalOrNull(c[startIndex + 8]),

            ROhm = Convert.ToDecimal(r),
            XOhm = Convert.ToDecimal(x),
            GammaReal = Convert.ToDecimal(gammaReal),
            GammaImag = Convert.ToDecimal(gammaImag),
            GammaMag = Convert.ToDecimal(gammaMag),
            Vswr = Convert.ToDecimal(vswr),

            //ZText = TrimToLength(NullIfEmpty(c[startIndex + 9]), 40),
            //ZNormalized = TrimToLength(NullIfEmpty(c[startIndex + 10]), 40),

            ZText = zText,
            ZNormalized = zNormalized,

            ForwardPowerW = forwardPower,
            ReflectedPowerW = reflectedPower,
            DeliveredPowerW = deliveredPower,
            ReturnLossDb = ComputeReturnLossDb(Convert.ToDecimal(gammaMag), forwardPower, reflectedPower),
            EfficiencyPct = ComputeEfficiencyPct(forwardPower, deliveredPower)
        };
    }

    private static SmithChartPointRecord ParseSmithChartPointB(IReadOnlyList<string> c, RfChannel channel)
    {
        //var gammaMag = ParseDecimalOrNull(c[startIndex + 7]);
        //var forwardPower = ParseDecimalOrNull(c[startIndex + 11]);
        //var reflectedPower = ParseDecimalOrNull(c[startIndex + 12]);
        //var deliveredPower = ParseDecimalOrNull(c[startIndex + 13]);
        var forwardPower = ParseDecimalOrNull(c[16]);
        var reflectedPower = ParseDecimalOrNull(c[17]);
        var deliveredPower = ParseDecimalOrNull(c[21]);


        double z0 = 50.0;
        double r = CalcR(vrms: Convert.ToDouble(ParseDecimalOrNull(c[18]) ?? 0m), irms: Convert.ToDouble(ParseDecimalOrNull(c[19]) ?? 0m), phaseDeg: Convert.ToDouble(ParseDecimalOrNull(c[20]) ?? 0m));
        double x = CalcX(vrms: Convert.ToDouble(ParseDecimalOrNull(c[18]) ?? 0m), irms: Convert.ToDouble(ParseDecimalOrNull(c[19]) ?? 0m), phaseDeg: Convert.ToDouble(ParseDecimalOrNull(c[20]) ?? 0m));
        double gammaReal = CalcGammaReal(r, x, z0);
        double gammaImag = CalcGammaImag(r, x, z0);
        double gammaMag = CalcGammaMag(gammaReal, gammaImag);
        double vswr = CalcVSWR(gammaMag);

        string zText = CalcZText(r, x);
        string zNormalized = CalcZNormalized(r, x, z0);

        return new SmithChartPointRecord
        {
            Channel = channel,
            //VoutVrms = ParseDecimalOrNull(c[startIndex]),
            //IoutArms = ParseDecimalOrNull(c[startIndex + 1]),
            //PhaseDeg = ParseDecimalOrNull(c[startIndex + 2]),
            VoutVrms = ParseDecimalOrNull(c[18]),
            IoutArms = ParseDecimalOrNull(c[19]),
            PhaseDeg = ParseDecimalOrNull(c[20]),

            //ROhm = ParseDecimalOrNull(c[startIndex + 3]),
            //XOhm = ParseDecimalOrNull(c[startIndex + 4]),
            //GammaReal = ParseDecimalOrNull(c[startIndex + 5]),
            // GammaImag = ParseDecimalOrNull(c[startIndex + 6]),
            //GammaMag = Convert.ToDecimal(gammaMag),
            //Vswr = ParseDecimalOrNull(c[startIndex + 8]),

            ROhm = Convert.ToDecimal(r),
            XOhm = Convert.ToDecimal(x),
            GammaReal = Convert.ToDecimal(gammaReal),
            GammaImag = Convert.ToDecimal(gammaImag),
            GammaMag = Convert.ToDecimal(gammaMag),
            Vswr = Convert.ToDecimal(vswr),

           // ZText = TrimToLength(NullIfEmpty(c[startIndex + 9]), 40),
           // ZNormalized = TrimToLength(NullIfEmpty(c[startIndex + 10]), 40),

            ZText = zText,
            ZNormalized = zNormalized,

            ForwardPowerW = forwardPower,
            ReflectedPowerW = reflectedPower,
            DeliveredPowerW = deliveredPower,
            ReturnLossDb = ComputeReturnLossDb(Convert.ToDecimal(gammaMag), forwardPower, reflectedPower),
            EfficiencyPct = ComputeEfficiencyPct(forwardPower, deliveredPower)
        };
    }

    private static decimal? ComputeReturnLossDb(decimal? gammaMag, decimal? forwardPower, decimal? reflectedPower)
    {
        var ratio = gammaMag;

        if (!ratio.HasValue && forwardPower.HasValue && reflectedPower.HasValue && forwardPower.Value > 0 && reflectedPower.Value >= 0)
        {
            ratio = (decimal)Math.Sqrt((double)(reflectedPower.Value / forwardPower.Value));
        }

        if (!ratio.HasValue || ratio.Value <= 0 || ratio.Value >= 1)
        {
            return null;
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
