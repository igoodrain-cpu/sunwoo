using MeasurementImporterService;
using MeasurementImporterService.Services;
using Serilog;

var builder = Host.CreateApplicationBuilder(args);

// -----------------------------------------------------------------
// 서비스 호스팅 등록: 같은 코드가 Windows 서비스로도, Linux systemd 서비스로도 동작한다.
// - Windows: sc.exe 로 등록 시 자동으로 Windows Service 모드로 인식됨
// - Linux:   systemd 유닛으로 등록 시 자동으로 systemd 모드로 인식됨
// - 둘 다 아니면(콘솔에서 직접 실행) 일반 콘솔 앱으로 동작
// -----------------------------------------------------------------
builder.Services.AddWindowsService(options =>
{
    options.ServiceName = "MeasurementImporterService";
});
builder.Services.AddSystemd();

// -----------------------------------------------------------------
// Serilog 구성 (appsettings.json의 "Serilog" 섹션을 그대로 사용)
// -----------------------------------------------------------------
Log.Logger = new LoggerConfiguration()
    .ReadFrom.Configuration(builder.Configuration)
    .Enrich.FromLogContext()
    .CreateLogger();

builder.Logging.ClearProviders();
builder.Services.AddSerilog();

// -----------------------------------------------------------------
// 옵션 바인딩
// -----------------------------------------------------------------
builder.Services.Configure<ImporterOptions>(
    builder.Configuration.GetSection(ImporterOptions.SectionName));

// -----------------------------------------------------------------
// 애플리케이션 서비스 등록
// -----------------------------------------------------------------
builder.Services.AddSingleton<CsvParserService>();

builder.Services.AddSingleton(sp =>
{
    var connectionString = builder.Configuration.GetConnectionString("MeasurementDb")
        ?? throw new InvalidOperationException("ConnectionStrings:MeasurementDb 설정이 없습니다.");

    var logger = sp.GetRequiredService<ILogger<PostgresRepository>>();
    return new PostgresRepository(connectionString, logger);
});

builder.Services.AddHostedService<Worker>();

try
{
    var host = builder.Build();
    await host.RunAsync();
}
catch (Exception ex)
{
    Log.Fatal(ex, "서비스가 예기치 못하게 종료되었습니다.");
    throw;
}
finally
{
    Log.CloseAndFlush();
}
