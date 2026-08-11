using MeasurementImporterService.Models;
using Microsoft.Extensions.Logging;
using Npgsql;
using NpgsqlTypes;

namespace MeasurementImporterService.Services;

public sealed class PostgresRepository
{
    private readonly string _connectionString;
    private readonly ILogger<PostgresRepository> _logger;

    public PostgresRepository(string connectionString, ILogger<PostgresRepository> logger)
    {
        _connectionString = connectionString;
        _logger = logger;
    }

    public async Task EnsureSchemaAsync(CancellationToken cancellationToken)
    {
        const string ddl = """
            DO $$
            BEGIN
                CREATE TYPE rf_channel AS ENUM ('source', 'bias');
            EXCEPTION
                WHEN duplicate_object THEN NULL;
            END $$;

            CREATE TABLE IF NOT EXISTS process_run (
                run_id           BIGSERIAL PRIMARY KEY,
                run_name         VARCHAR(100) NOT NULL UNIQUE,
                recipe_name      VARCHAR(100),
                equipment_id     VARCHAR(50),
                started_at       TIMESTAMP,
                ended_at         TIMESTAMP,
                created_at       TIMESTAMP NOT NULL DEFAULT now()
            );

            CREATE TABLE IF NOT EXISTS process_step (
                step_id              BIGSERIAL PRIMARY KEY,
                run_id               BIGINT NOT NULL REFERENCES process_run(run_id) ON DELETE CASCADE,
                step_num             SMALLINT NOT NULL,
                step_name            VARCHAR(20) NOT NULL,
                log_date             DATE NOT NULL,
                log_time             TIME(3) NOT NULL,
                srf_freq             NUMERIC(8,3),
                s_fwd                NUMERIC(10,3),
                s_ref                NUMERIC(10,3),
                s_vrms               NUMERIC(10,3),
                s_irms               NUMERIC(10,4),
                s_phase              NUMERIC(6,2),
                s_delivered_pwr      NUMERIC(10,3),
                s_preset_load        NUMERIC(6,2),
                s_preset_tune        NUMERIC(6,2),
                s_load_pos           NUMERIC(6,2),
                s_tune_pos           NUMERIC(6,2),
                br_freq              NUMERIC(8,3),
                b_fwd                NUMERIC(10,3),
                b_ref                NUMERIC(10,3),
                b_vrms               NUMERIC(10,3),
                b_irms               NUMERIC(10,4),
                b_phase              NUMERIC(6,2),
                b_delivered_pwr      NUMERIC(10,3),
                b_preset_load        NUMERIC(6,2),
                b_preset_tune        NUMERIC(6,2),
                b_load_pos           NUMERIC(6,2),
                b_tune_pos           NUMERIC(6,2),
                ar_flow              NUMERIC(8,2),
                o2_flow              NUMERIC(8,2),
                apc_pressure         NUMERIC(8,2),
                apc_position         NUMERIC(8,2),
                vvc1                 NUMERIC(8,2),
                vvc2                 NUMERIC(8,2),
                vvc3                 NUMERIC(8,2),
                proc_status          SMALLINT NOT NULL
            );

            CREATE INDEX IF NOT EXISTS idx_process_step_run_id ON process_step (run_id);
            CREATE INDEX IF NOT EXISTS idx_process_step_log_date_time ON process_step (log_date, log_time);

            CREATE TABLE IF NOT EXISTS smith_chart_point (
                point_id             BIGSERIAL PRIMARY KEY,
                step_id              BIGINT NOT NULL REFERENCES process_step(step_id) ON DELETE CASCADE,
                channel              rf_channel NOT NULL,
                vout_vrms            NUMERIC(10,4),
                iout_arms            NUMERIC(10,4),
                phase_deg            NUMERIC(6,2),
                r_ohm                NUMERIC(12,4),
                x_ohm                NUMERIC(12,4),
                gamma_real           NUMERIC(9,6),
                gamma_imag           NUMERIC(9,6),
                gamma_mag            NUMERIC(9,6),
                vswr                 NUMERIC(9,3),
                z_text               VARCHAR(40),
                z_normalized         VARCHAR(40),
                forward_p_w          NUMERIC(10,4),
                reflected_p_w        NUMERIC(10,4),
                delivered_p_w        NUMERIC(10,4),
                return_loss_db       NUMERIC(6,2),
                efficiency_pct       NUMERIC(6,2),
                CONSTRAINT uq_smith_chart_point_step_channel UNIQUE (step_id, channel)
            );

            CREATE INDEX IF NOT EXISTS idx_smith_chart_point_step_id ON smith_chart_point (step_id);

            CREATE TABLE IF NOT EXISTS import_file_log (
                id              BIGSERIAL PRIMARY KEY,
                file_name       TEXT NOT NULL UNIQUE,
                file_hash       TEXT NOT NULL,
                row_count       INTEGER NOT NULL,
                status          TEXT NOT NULL,
                error_message   TEXT,
                processed_at    TIMESTAMPTZ NOT NULL DEFAULT now()
            );
            """;

        await using var conn = new NpgsqlConnection(_connectionString);
        await conn.OpenAsync(cancellationToken);
        await using var cmd = new NpgsqlCommand(ddl, conn);
        await cmd.ExecuteNonQueryAsync(cancellationToken);
    }

    public async Task<bool> IsAlreadyProcessedAsync(string fileHash, CancellationToken cancellationToken)
    {
        const string sql = """
            SELECT EXISTS(
                SELECT 1 FROM import_file_log
                WHERE file_hash = @hash AND status = 'SUCCESS'
            );
            """;

        await using var conn = new NpgsqlConnection(_connectionString);
        await conn.OpenAsync(cancellationToken);
        await using var cmd = new NpgsqlCommand(sql, conn);
        cmd.Parameters.AddWithValue("hash", fileHash);

        var result = await cmd.ExecuteScalarAsync(cancellationToken);
        return result is true;
    }

    public async Task InsertBatchAsync(MeasurementBatch batch, CancellationToken cancellationToken)
    {
        await using var conn = new NpgsqlConnection(_connectionString);
        await conn.OpenAsync(cancellationToken);
        await using var tx = await conn.BeginTransactionAsync(cancellationToken);

        try
        {
            var runId = await InsertProcessRunAsync(conn, tx, batch, cancellationToken);

            foreach (var step in batch.Steps)
            {
                var stepId = await InsertProcessStepAsync(conn, tx, runId, step, cancellationToken);

                if (step.SourcePoint.HasValues)
                {
                    await InsertSmithChartPointAsync(conn, tx, stepId, step.SourcePoint, cancellationToken);
                }

                if (step.BiasPoint.HasValues)
                {
                    await InsertSmithChartPointAsync(conn, tx, stepId, step.BiasPoint, cancellationToken);
                }
            }

            const string logSql = """
                INSERT INTO import_file_log (file_name, file_hash, row_count, status)
                VALUES (@file_name, @file_hash, @row_count, 'SUCCESS')
                ON CONFLICT (file_name) DO UPDATE
                    SET file_hash = EXCLUDED.file_hash,
                        row_count = EXCLUDED.row_count,
                        status = 'SUCCESS',
                        error_message = NULL,
                        processed_at = now();
                """;

            await using (var cmd = new NpgsqlCommand(logSql, conn, tx))
            {
                cmd.Parameters.AddWithValue("file_name", batch.SourceFile);
                cmd.Parameters.AddWithValue("file_hash", batch.FileHash);
                cmd.Parameters.AddWithValue("row_count", batch.Steps.Count);
                await cmd.ExecuteNonQueryAsync(cancellationToken);
            }

            await tx.CommitAsync(cancellationToken);

            _logger.LogInformation(
                "배치 저장 완료: file={File}, runName={RunName}, steps={Steps}",
                batch.SourceFile, batch.RunName, batch.Steps.Count);
        }
        catch
        {
            await tx.RollbackAsync(cancellationToken);
            throw;
        }
    }

    public async Task LogFailureAsync(string fileName, string fileHash, string errorMessage, CancellationToken cancellationToken)
    {
        const string sql = """
            INSERT INTO import_file_log (file_name, file_hash, row_count, status, error_message)
            VALUES (@file_name, @file_hash, 0, 'FAILED', @error_message)
            ON CONFLICT (file_name) DO UPDATE
                SET file_hash = EXCLUDED.file_hash,
                    status = 'FAILED',
                    error_message = EXCLUDED.error_message,
                    processed_at = now();
            """;

        try
        {
            await using var conn = new NpgsqlConnection(_connectionString);
            await conn.OpenAsync(cancellationToken);
            await using var cmd = new NpgsqlCommand(sql, conn);
            cmd.Parameters.AddWithValue("file_name", fileName);
            cmd.Parameters.AddWithValue("file_hash", fileHash);
            cmd.Parameters.AddWithValue("error_message", errorMessage);
            await cmd.ExecuteNonQueryAsync(cancellationToken);
        }
        catch (Exception ex)
        {
            _logger.LogError(ex, "실패 이력 기록 중 오류 발생: {FileName}", fileName);
        }
    }

    private static async Task<long> InsertProcessRunAsync(
        NpgsqlConnection conn,
        NpgsqlTransaction tx,
        MeasurementBatch batch,
        CancellationToken cancellationToken)
    {
        const string sql = """
            INSERT INTO process_run (run_name, recipe_name, equipment_id, started_at, ended_at)
            VALUES (@run_name, @recipe_name, @equipment_id, @started_at, @ended_at)
            RETURNING run_id;
            """;

        await using var cmd = new NpgsqlCommand(sql, conn, tx);
        cmd.Parameters.AddWithValue("run_name", batch.RunName);
        AddNullableText(cmd, "recipe_name", batch.RecipeName, 100);
        AddNullableText(cmd, "equipment_id", batch.EquipmentId, 50);
        cmd.Parameters.AddWithValue("started_at", NpgsqlDbType.Timestamp, batch.StartedAt);
        cmd.Parameters.AddWithValue("ended_at", NpgsqlDbType.Timestamp, batch.EndedAt);

        var result = await cmd.ExecuteScalarAsync(cancellationToken);
        return Convert.ToInt64(result);
    }

    private static async Task<long> InsertProcessStepAsync(
        NpgsqlConnection conn,
        NpgsqlTransaction tx,
        long runId,
        ProcessStepRecord step,
        CancellationToken cancellationToken)
    {
        const string sql = """
            INSERT INTO process_step (
                run_id, step_num, step_name, log_date, log_time,
                srf_freq, s_fwd, s_ref, s_vrms, s_irms, s_phase, s_delivered_pwr,
                s_preset_load, s_preset_tune, s_load_pos, s_tune_pos,
                br_freq, b_fwd, b_ref, b_vrms, b_irms, b_phase, b_delivered_pwr,
                b_preset_load, b_preset_tune, b_load_pos, b_tune_pos,
                ar_flow, o2_flow, apc_pressure, apc_position, vvc1, vvc2, vvc3, proc_status
            )
            VALUES (
                @run_id, @step_num, @step_name, @log_date, @log_time,
                @srf_freq, @s_fwd, @s_ref, @s_vrms, @s_irms, @s_phase, @s_delivered_pwr,
                @s_preset_load, @s_preset_tune, @s_load_pos, @s_tune_pos,
                @br_freq, @b_fwd, @b_ref, @b_vrms, @b_irms, @b_phase, @b_delivered_pwr,
                @b_preset_load, @b_preset_tune, @b_load_pos, @b_tune_pos,
                @ar_flow, @o2_flow, @apc_pressure, @apc_position, @vvc1, @vvc2, @vvc3, @proc_status
            )
            RETURNING step_id;
            """;

        await using var cmd = new NpgsqlCommand(sql, conn, tx);
        cmd.Parameters.AddWithValue("run_id", NpgsqlDbType.Bigint, runId);
        cmd.Parameters.AddWithValue("step_num", NpgsqlDbType.Smallint, step.StepNum);
        cmd.Parameters.AddWithValue("step_name", step.StepName);
        cmd.Parameters.AddWithValue("log_date", NpgsqlDbType.Date, step.LogDate);
        cmd.Parameters.AddWithValue("log_time", NpgsqlDbType.Time, step.LogTime);
        AddNullableNumeric(cmd, "srf_freq", step.SrfFreq);
        AddNullableNumeric(cmd, "s_fwd", step.SFwd);
        AddNullableNumeric(cmd, "s_ref", step.SRef);
        AddNullableNumeric(cmd, "s_vrms", step.SVrms);
        AddNullableNumeric(cmd, "s_irms", step.SIrms);
        AddNullableNumeric(cmd, "s_phase", step.SPhase);
        AddNullableNumeric(cmd, "s_delivered_pwr", step.SDeliveredPwr);
        AddNullableNumeric(cmd, "s_preset_load", step.SPresetLoad);
        AddNullableNumeric(cmd, "s_preset_tune", step.SPresetTune);
        AddNullableNumeric(cmd, "s_load_pos", step.SLoadPos);
        AddNullableNumeric(cmd, "s_tune_pos", step.STunePos);
        AddNullableNumeric(cmd, "br_freq", step.BrFreq);
        AddNullableNumeric(cmd, "b_fwd", step.BFwd);
        AddNullableNumeric(cmd, "b_ref", step.BRef);
        AddNullableNumeric(cmd, "b_vrms", step.BVrms);
        AddNullableNumeric(cmd, "b_irms", step.BIrms);
        AddNullableNumeric(cmd, "b_phase", step.BPhase);
        AddNullableNumeric(cmd, "b_delivered_pwr", step.BDeliveredPwr);
        AddNullableNumeric(cmd, "b_preset_load", step.BPresetLoad);
        AddNullableNumeric(cmd, "b_preset_tune", step.BPresetTune);
        AddNullableNumeric(cmd, "b_load_pos", step.BLoadPos);
        AddNullableNumeric(cmd, "b_tune_pos", step.BTunePos);
        AddNullableNumeric(cmd, "ar_flow", step.ArFlow);
        AddNullableNumeric(cmd, "o2_flow", step.O2Flow);
        AddNullableNumeric(cmd, "apc_pressure", step.ApcPressure);
        AddNullableNumeric(cmd, "apc_position", step.ApcPosition);
        AddNullableNumeric(cmd, "vvc1", step.Vvc1);
        AddNullableNumeric(cmd, "vvc2", step.Vvc2);
        AddNullableNumeric(cmd, "vvc3", step.Vvc3);
        cmd.Parameters.AddWithValue("proc_status", NpgsqlDbType.Smallint, step.ProcStatus);

        var result = await cmd.ExecuteScalarAsync(cancellationToken);
        return Convert.ToInt64(result);
    }

    private static async Task InsertSmithChartPointAsync(
        NpgsqlConnection conn,
        NpgsqlTransaction tx,
        long stepId,
        SmithChartPointRecord point,
        CancellationToken cancellationToken)
    {
        const string sql = """
            INSERT INTO smith_chart_point (
                step_id, channel, vout_vrms, iout_arms, phase_deg, r_ohm, x_ohm,
                gamma_real, gamma_imag, gamma_mag, vswr, z_text, z_normalized,
                forward_p_w, reflected_p_w, delivered_p_w, return_loss_db, efficiency_pct
            )
            VALUES (
                @step_id, @channel::rf_channel, @vout_vrms, @iout_arms, @phase_deg, @r_ohm, @x_ohm,
                @gamma_real, @gamma_imag, @gamma_mag, @vswr, @z_text, @z_normalized,
                @forward_p_w, @reflected_p_w, @delivered_p_w, @return_loss_db, @efficiency_pct
            );
            """;

        await using var cmd = new NpgsqlCommand(sql, conn, tx);
        cmd.Parameters.AddWithValue("step_id", NpgsqlDbType.Bigint, stepId);
        cmd.Parameters.AddWithValue("channel", NpgsqlDbType.Text, point.Channel == RfChannel.Source ? "source" : "bias");
        AddNullableNumeric(cmd, "vout_vrms", point.VoutVrms);
        AddNullableNumeric(cmd, "iout_arms", point.IoutArms);
        AddNullableNumeric(cmd, "phase_deg", point.PhaseDeg);
        AddNullableNumeric(cmd, "r_ohm", point.ROhm);
        AddNullableNumeric(cmd, "x_ohm", point.XOhm);
        AddNullableNumeric(cmd, "gamma_real", point.GammaReal);
        AddNullableNumeric(cmd, "gamma_imag", point.GammaImag);
        AddNullableNumeric(cmd, "gamma_mag", point.GammaMag);
        AddNullableNumeric(cmd, "vswr", point.Vswr);
        AddNullableText(cmd, "z_text", point.ZText, 40);
        AddNullableText(cmd, "z_normalized", point.ZNormalized, 40);
        AddNullableNumeric(cmd, "forward_p_w", point.ForwardPowerW);
        AddNullableNumeric(cmd, "reflected_p_w", point.ReflectedPowerW);
        AddNullableNumeric(cmd, "delivered_p_w", point.DeliveredPowerW);
        AddNullableNumeric(cmd, "return_loss_db", point.ReturnLossDb);
        AddNullableNumeric(cmd, "efficiency_pct", point.EfficiencyPct);
        await cmd.ExecuteNonQueryAsync(cancellationToken);
    }

    private static void AddNullableNumeric(NpgsqlCommand cmd, string name, decimal? value)
    {
        cmd.Parameters.AddWithValue(name, NpgsqlDbType.Numeric, (object?)value ?? DBNull.Value);
    }

    private static void AddNullableText(NpgsqlCommand cmd, string name, string? value, int length)
    {
        var parameter = cmd.Parameters.Add(name, NpgsqlDbType.Varchar);
        parameter.Size = length;
        parameter.Value = string.IsNullOrEmpty(value)
            ? DBNull.Value
            : value.Length <= length
                ? value
                : value[..length];
    }
}
