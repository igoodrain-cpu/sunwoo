# Measurement Importer Service

RF 임피던스/파워 측정 CSV 파일을 폴더 감시 방식으로 읽어들여 PostgreSQL에 저장하는 백그라운드 서비스입니다.
.NET 8 Worker Service 기반이며, **Windows 서비스**와 **Linux systemd 서비스** 양쪽 모두 동일한 코드로 등록/구동할 수 있습니다.

## 동작 방식

1. `ImporterOptions:IncomingFolder` 폴더를 주기적으로(`PollingIntervalSeconds`) 스캔
2. 최근 수정된 지 얼마 안 된 파일(장비가 아직 쓰는 중일 수 있음)은 건너뛰고, 안정된 CSV만 처리
3. CSV를 파싱 → SHA-256 해시로 동일 파일 중복 처리 방지 → `process_run` / `process_step` / `smith_chart_point`에 insert
4. 성공하면 `BackupFolder`(없으면 `ProcessedFolder`)로, 실패하면 `ErrorFolder`로 원본 파일 이동
5. 모든 처리 이력은 `import_file_log` 테이블에 기록 (재처리 판단 및 감사용)

## 프로젝트 구조

```
MeasurementImporterService/
├── Program.cs                  # 진입점 (Generic Host, Windows Service/systemd 등록)
├── Worker.cs                   # 폴링 루프 (BackgroundService)
├── Models/
│   └── MeasurementRecord.cs    # CSV 1행 -> DB 레코드 매핑 모델
├── Services/
│   ├── ImporterOptions.cs      # appsettings.json 바인딩용 옵션
│   ├── CsvParserService.cs     # CSV 파싱, 해시 계산
│   └── PostgresRepository.cs   # 스키마 생성, 중복 체크, ERD 기준 insert
├── sql/schema.sql               # 참고용 DDL (서비스가 첫 실행 시 자동 생성도 함)
├── appsettings.json
└── MeasurementImporterService.csproj
```

## 1. 사전 준비

### PostgreSQL
```sql
CREATE DATABASE measurement_db;
CREATE USER measurement_user WITH PASSWORD 'CHANGE_ME';
GRANT ALL PRIVILEGES ON DATABASE measurement_db TO measurement_user;
```
테이블은 서비스가 최초 기동 시 `EnsureSchemaAsync()`로 자동 생성합니다.
DBA가 직접 관리하고 싶다면 `sql/schema.sql`을 실행한 뒤, `Program.cs`에서
`AddHostedService<Worker>()` 이전에 있는 `EnsureSchemaAsync` 호출을 제거하세요.

### appsettings.json 수정
```json
{
  "ConnectionStrings": {
    "MeasurementDb": "Host=localhost;Port=5432;Database=measurement_db;Username=measurement_user;Password=CHANGE_ME"
  },
  "ImporterOptions": {
    "IncomingFolder": "/data/measurement/incoming",   // 실제 환경 경로로 변경 (Windows는 C:\\... 형식)
    "BackupFolder": "/data/measurement/backup",
    "ProcessedFolder": "/data/measurement/processed",
    "ErrorFolder": "/data/measurement/error",
    "DefaultRecipeName": "DEFAULT_RECIPE",
    "DefaultEquipmentId": "EQ-01",
    "PollingIntervalSeconds": 5
  }
}
```
운영 환경에서는 비밀번호를 appsettings.json에 평문으로 두지 말고,
환경변수(`ConnectionStrings__MeasurementDb`)나 `dotnet user-secrets`, 또는 Windows/Linux의
시크릿 관리 도구를 사용하는 것을 권장합니다.

## 2. 빌드

```bash
dotnet restore
dotnet publish -c Release -r win-x64 --self-contained false -o ./publish        # Windows 서비스용
dotnet publish -c Release -r linux-x64 --self-contained false -o ./publish      # Linux 서비스용
```

## 3. Windows 서비스로 등록

관리자 권한 PowerShell/CMD에서:
```cmd
sc.exe create MeasurementImporterService binPath= "C:\Deploy\MeasurementImporterService\MeasurementImporterService.exe" start= auto
sc.exe description MeasurementImporterService "측정 CSV -> PostgreSQL 적재 서비스"
sc.exe start MeasurementImporterService
```
- 로그 확인: `logs\measurement-importer-*.log` (appsettings.json의 Serilog File sink 경로)
- 이벤트 뷰어(Windows 이벤트 로그)에도 서비스 시작/중지 이벤트가 남습니다(`AddWindowsService` 덕분).
- 서비스 제거: `sc.exe delete MeasurementImporterService`

## 4. Linux systemd 서비스로 등록

`/etc/systemd/system/measurement-importer.service`:
```ini
[Unit]
Description=Measurement Importer Service
After=network.target postgresql.service

[Service]
Type=notify
ExecStart=/usr/bin/dotnet /opt/measurement-importer/MeasurementImporterService.dll
WorkingDirectory=/opt/measurement-importer
Restart=always
RestartSec=5
User=measurement-svc
Environment=DOTNET_ENVIRONMENT=Production

[Install]
WantedBy=multi-user.target
```
```bash
sudo systemctl daemon-reload
sudo systemctl enable --now measurement-importer.service
sudo systemctl status measurement-importer.service
journalctl -u measurement-importer.service -f
```
`AddSystemd()`가 systemd의 `Type=notify` 프로토콜(sd_notify)을 자동 처리하므로,
systemd가 서비스의 시작 완료/정지를 정확히 인지합니다.

## 5. 확장 아이디어

- **파일 워처(FileSystemWatcher) 방식**으로 전환: 폴링 대신 이벤트 기반으로 즉시 반응하고 싶다면 교체 가능하지만,
  네트워크 드라이브나 대용량 파일 쓰기 도중 이벤트가 씹히는 경우가 있어 현재는 폴링+안정성 체크 방식을 권장합니다.
- **재시도 정책**: Postgres 연결 실패 시 Polly 등으로 지수 백오프 재시도 추가 가능
- **배치 크기 제한**: 매우 큰 CSV(수십만 행)의 경우 COPY를 청크 단위로 나눠 커밋하도록 조정 가능
- **알림 연동**: `LogFailureAsync` 실패 이벤트에 Slack/이메일 알림 훅 추가

## 참고: 공정 CSV 컬럼 매핑

상위 34개 컬럼은 `process_step`, 이후 `S.*` 14개 컬럼은 `smith_chart_point(channel='source')`,
`B.*` 14개 컬럼은 `smith_chart_point(channel='bias')`로 저장됩니다.
