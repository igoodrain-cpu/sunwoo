namespace MeasurementImporterService.Services;

public sealed class ImporterOptions
{
    public const string SectionName = "ImporterOptions";

    public string IncomingFolder { get; set; } = string.Empty;
    public string BackupFolder { get; set; } = string.Empty;
    public string ProcessedFolder { get; set; } = string.Empty;
    public string ErrorFolder { get; set; } = string.Empty;
    public string? DefaultRecipeName { get; set; }
    public string? DefaultEquipmentId { get; set; }
    public int PollingIntervalSeconds { get; set; } = 5;
    public string FileSearchPattern { get; set; } = "*.csv";

    /// <summary>
    /// 파일이 아직 쓰여지는 중(장비 프로그램이 저장 중)인 상태에서 읽는 것을 방지하기 위해,
    /// 마지막 수정시각으로부터 이 값(ms) 이상 지난 파일만 처리 대상으로 간주한다.
    /// </summary>
    public int MinFileAgeMilliseconds { get; set; } = 1000;
}
