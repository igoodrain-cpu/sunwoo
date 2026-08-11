using MeasurementImporterService.Services;
using Microsoft.Extensions.Options;

namespace MeasurementImporterService;

public sealed class Worker : BackgroundService
{
    private readonly ILogger<Worker> _logger;
    private readonly ImporterOptions _options;
    private readonly CsvParserService _parser;
    private readonly PostgresRepository _repository;

    public Worker(
        ILogger<Worker> logger,
        IOptions<ImporterOptions> options,
        CsvParserService parser,
        PostgresRepository repository)
    {
        _logger = logger;
        _options = options.Value;
        _parser = parser;
        _repository = repository;
    }

    protected override async Task ExecuteAsync(CancellationToken stoppingToken)
    {
        EnsureFolders();

        _logger.LogInformation("Measurement Importer Service 시작. Incoming={Incoming}, Interval={Interval}s",
            _options.IncomingFolder, _options.PollingIntervalSeconds);

        await _repository.EnsureSchemaAsync(stoppingToken);

        while (!stoppingToken.IsCancellationRequested)
        {
            try
            {
                await ProcessIncomingFilesAsync(stoppingToken);
            }
            catch (Exception ex)
            {
                // 폴링 루프 자체는 절대 죽으면 안 되므로, 예기치 못한 예외는 로그만 남기고 계속 진행한다.
                _logger.LogError(ex, "폴링 처리 중 예기치 못한 오류가 발생했습니다.");
            }

            try
            {
                await Task.Delay(TimeSpan.FromSeconds(_options.PollingIntervalSeconds), stoppingToken);
            }
            catch (OperationCanceledException)
            {
                // 서비스 종료 요청 시 정상적으로 루프를 빠져나간다.
                break;
            }
        }

        _logger.LogInformation("Measurement Importer Service 종료.");
    }

    private void EnsureFolders()
    {
        Directory.CreateDirectory(_options.IncomingFolder);
        Directory.CreateDirectory(GetBackupFolder());
        Directory.CreateDirectory(_options.ErrorFolder);
    }

    private async Task ProcessIncomingFilesAsync(CancellationToken stoppingToken)
    {
        var files = Directory.EnumerateFiles(_options.IncomingFolder, _options.FileSearchPattern)
            .Where(IsFileStable)
            .OrderBy(f => f)
            .ToList();

        foreach (var filePath in files)
        {
            if (stoppingToken.IsCancellationRequested)
            {
                break;
            }

            await ProcessSingleFileAsync(filePath, stoppingToken);
        }
    }

    /// <summary>
    /// 장비/다른 프로그램이 아직 쓰고 있는 파일을 건드리지 않도록,
    /// 마지막 수정시각으로부터 일정 시간이 지난 파일만 "안정적"이라고 판단한다.
    /// </summary>
    private bool IsFileStable(string filePath)
    {
        var lastWrite = File.GetLastWriteTimeUtc(filePath);
        var age = DateTime.UtcNow - lastWrite;
        return age.TotalMilliseconds >= _options.MinFileAgeMilliseconds;
    }

    private async Task ProcessSingleFileAsync(string filePath, CancellationToken stoppingToken)
    {
        var fileName = Path.GetFileName(filePath);
        _logger.LogInformation("파일 처리 시작: {FileName}", fileName);

        try
        {
            var batch = await _parser.ParseAsync(
                filePath,
                _options.DefaultRecipeName,
                _options.DefaultEquipmentId,
                stoppingToken);

            if (await _repository.IsAlreadyProcessedAsync(batch.FileHash, stoppingToken))
            {
                _logger.LogWarning("이미 처리된 파일입니다 (내용 동일). 스킵 후 backup 폴더로 이동: {FileName}", fileName);
                MoveFile(filePath, GetBackupFolder());
                return;
            }

            await _repository.InsertBatchAsync(batch, stoppingToken);
            MoveFile(filePath, GetBackupFolder());

            _logger.LogInformation("파일 처리 완료: {FileName} ({RowCount} steps)", fileName, batch.Steps.Count);
        }
        catch (Exception ex)
        {
            _logger.LogError(ex, "파일 처리 실패: {FileName}", fileName);

            var fileHash = await TryComputeHashAsync(filePath, stoppingToken);
            await _repository.LogFailureAsync(fileName, fileHash, ex.Message, stoppingToken);
            MoveFile(filePath, _options.ErrorFolder);
        }
    }

    private async Task<string> TryComputeHashAsync(string filePath, CancellationToken stoppingToken)
    {
        try
        {
            return await _parser.ComputeFileHashAsync(filePath, stoppingToken);
        }
        catch
        {
            return "unknown";
        }
    }

    private void MoveFile(string filePath, string destinationFolder)
    {
        var fileName = Path.GetFileName(filePath);
        var destination = Path.Combine(destinationFolder, fileName);

        // 동일 이름 파일이 이미 있으면 타임스탬프를 붙여 덮어쓰기를 방지한다.
        if (File.Exists(destination))
        {
            var timestamp = DateTime.UtcNow.ToString("yyyyMMddHHmmssfff");
            destination = Path.Combine(destinationFolder,
                $"{Path.GetFileNameWithoutExtension(fileName)}_{timestamp}{Path.GetExtension(fileName)}");
        }

        File.Move(filePath, destination);
    }

    private string GetBackupFolder() =>
        string.IsNullOrWhiteSpace(_options.BackupFolder)
            ? _options.ProcessedFolder
            : _options.BackupFolder;
}
