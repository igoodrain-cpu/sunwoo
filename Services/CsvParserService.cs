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
    private const int ExpectedColumnCount = 62;

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
        var sourcePoint = ParseSmithChartPoint(c, 34, RfChannel.Source);
        var biasPoint = ParseSmithChartPoint(c, 48, RfChannel.Bias);

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

    private static SmithChartPointRecord ParseSmithChartPoint(IReadOnlyList<string> c, int startIndex, RfChannel channel)
    {
        var gammaMag = ParseDecimalOrNull(c[startIndex + 7]);
        var forwardPower = ParseDecimalOrNull(c[startIndex + 11]);
        var reflectedPower = ParseDecimalOrNull(c[startIndex + 12]);
        var deliveredPower = ParseDecimalOrNull(c[startIndex + 13]);

        return new SmithChartPointRecord
        {
            Channel = channel,
            VoutVrms = ParseDecimalOrNull(c[startIndex]),
            IoutArms = ParseDecimalOrNull(c[startIndex + 1]),
            PhaseDeg = ParseDecimalOrNull(c[startIndex + 2]),
            ROhm = ParseDecimalOrNull(c[startIndex + 3]),
            XOhm = ParseDecimalOrNull(c[startIndex + 4]),
            GammaReal = ParseDecimalOrNull(c[startIndex + 5]),
            GammaImag = ParseDecimalOrNull(c[startIndex + 6]),
            GammaMag = gammaMag,
            Vswr = ParseDecimalOrNull(c[startIndex + 8]),
            ZText = TrimToLength(NullIfEmpty(c[startIndex + 9]), 40),
            ZNormalized = TrimToLength(NullIfEmpty(c[startIndex + 10]), 40),
            ForwardPowerW = forwardPower,
            ReflectedPowerW = reflectedPower,
            DeliveredPowerW = deliveredPower,
            ReturnLossDb = ComputeReturnLossDb(gammaMag, forwardPower, reflectedPower),
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
}
