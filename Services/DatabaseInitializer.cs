using Npgsql;

namespace MeasurementImporterService.Services;

/// <summary>
/// 서비스 시작 시 대상 데이터베이스(예: measurement_db)가 없으면 자동으로 생성한다.
/// - CREATE DATABASE 는 대상 DB에 접속한 상태에서는 실행할 수 없으므로,
///   유지보수용 DB(postgres)에 접속해서 존재 여부 확인 후 생성한다.
/// - Worker 보다 먼저 등록되어야 한다. (IHostedService.StartAsync 는 등록 순서대로 실행되므로
///   이 작업이 끝난 뒤에 Worker → EnsureSchemaAsync 가 실행된다.)
/// - Windows 부팅 직후 PostgreSQL 서비스가 아직 안 올라온 경우를 대비해 접속 실패 시 재시도한다.
/// </summary>
public sealed class DatabaseInitializer : IHostedService
{
    private const string MaintenanceDatabase = "postgres";
    private const int MaxAttempts = 12;
    private static readonly TimeSpan RetryDelay = TimeSpan.FromSeconds(5);

    private readonly string _connectionString;
    private readonly ILogger<DatabaseInitializer> _logger;

    public DatabaseInitializer(string connectionString, ILogger<DatabaseInitializer> logger)
    {
        _connectionString = connectionString;
        _logger = logger;
    }

    public async Task StartAsync(CancellationToken cancellationToken)
    {
        for (var attempt = 1; ; attempt++)
        {
            try
            {
                await EnsureDatabaseExistsAsync(cancellationToken);
                return;
            }
            catch (NpgsqlException ex) when (ex.IsTransient && attempt < MaxAttempts)
            {
                _logger.LogWarning(
                    "PostgreSQL 접속 실패 ({Attempt}/{MaxAttempts}). {Delay}초 후 재시도합니다. 사유: {Message}",
                    attempt, MaxAttempts, RetryDelay.TotalSeconds, ex.Message);
                await Task.Delay(RetryDelay, cancellationToken);
            }
        }
    }

    public Task StopAsync(CancellationToken cancellationToken) => Task.CompletedTask;

    private async Task EnsureDatabaseExistsAsync(CancellationToken cancellationToken)
    {
        var target = new NpgsqlConnectionStringBuilder(_connectionString);
        var databaseName = target.Database;

        if (string.IsNullOrWhiteSpace(databaseName))
            throw new InvalidOperationException("연결 문자열에 Database 항목이 없습니다.");

        // 유지보수 DB(postgres)로 접속. 1회성 작업이므로 풀링은 끈다.
        var admin = new NpgsqlConnectionStringBuilder(_connectionString)
        {
            Database = MaintenanceDatabase,
            Pooling = false
        };

        await using var conn = new NpgsqlConnection(admin.ConnectionString);
        await conn.OpenAsync(cancellationToken);

        await using (var check = new NpgsqlCommand(
            "SELECT 1 FROM pg_database WHERE datname = @name", conn))
        {
            check.Parameters.AddWithValue("name", databaseName);
            if (await check.ExecuteScalarAsync(cancellationToken) is not null)
            {
                _logger.LogInformation("데이터베이스 '{Database}' 확인 완료.", databaseName);
                return;
            }
        }

        _logger.LogWarning("데이터베이스 '{Database}' 가 없어 새로 생성합니다.", databaseName);

        // CREATE DATABASE 는 파라미터 바인딩이 불가하므로 식별자를 직접 이스케이프한다.
        var quotedName = "\"" + databaseName.Replace("\"", "\"\"") + "\"";
        var sql = $"CREATE DATABASE {quotedName} ENCODING 'UTF8' TEMPLATE template0";

        try
        {
            await using var create = new NpgsqlCommand(sql, conn);
            await create.ExecuteNonQueryAsync(cancellationToken);
            _logger.LogInformation("데이터베이스 '{Database}' 생성 완료.", databaseName);
        }
        catch (PostgresException ex) when (ex.SqlState == PostgresErrorCodes.DuplicateDatabase)
        {
            // 동시에 다른 프로세스가 먼저 만든 경우 — 정상으로 간주
            _logger.LogInformation("데이터베이스 '{Database}' 가 이미 생성되어 있습니다.", databaseName);
        }
        catch (PostgresException ex) when (ex.SqlState == PostgresErrorCodes.InsufficientPrivilege)
        {
            throw new InvalidOperationException(
                $"'{target.Username}' 계정에 CREATEDB 권한이 없어 '{databaseName}' 를 생성할 수 없습니다. " +
                "DB를 수동으로 생성하거나 ALTER ROLE ... CREATEDB 로 권한을 부여하세요.", ex);
        }
    }
}
