using System;
using System.Collections.Generic;
using System.Configuration;
using System.Globalization;
using Npgsql;

namespace Iruza
{
    internal class ProcessRunRecord
    {
        public long RunId { get; set; }
        public string RunName { get; set; }
        public string RecipeName { get; set; }
        public string EquipmentId { get; set; }
        public DateTime? StartedAt { get; set; }
        public DateTime? EndedAt { get; set; }
        public DateTime? CreatedAt { get; set; }
    }

    internal class ProcessStepRecord
    {
        public long StepId { get; set; }
        public long RunId { get; set; }
        public short StepNum { get; set; }
        public string StepName { get; set; }
        public DateTime? LogDate { get; set; }
        public TimeSpan? LogTime { get; set; }
        public decimal? SrfFreq { get; set; }
        public decimal? SFwd { get; set; }
        public decimal? SRef { get; set; }
        public decimal? SVrms { get; set; }
        public decimal? SIrms { get; set; }
        public decimal? SPhase { get; set; }
        public decimal? SDeliveredPwr { get; set; }
        public decimal? SPresetLoad { get; set; }
        public decimal? SPresetTune { get; set; }
        public decimal? SLoadPos { get; set; }
        public decimal? STunePos { get; set; }
        public decimal? BrfFreq { get; set; }
        public decimal? BFwd { get; set; }
        public decimal? BRef { get; set; }
        public decimal? BVrms { get; set; }
        public decimal? BIrms { get; set; }
        public decimal? BPhase { get; set; }
        public decimal? BDeliveredPwr { get; set; }
        public decimal? BPresetLoad { get; set; }
        public decimal? BPresetTune { get; set; }
        public decimal? BLoadPos { get; set; }
        public decimal? BTunePos { get; set; }
        public decimal? ArFlow { get; set; }
        public decimal? O2Flow { get; set; }
        public decimal? ApcPressure { get; set; }
        public decimal? ApcPosition { get; set; }
        public decimal? Vvc1 { get; set; }
        public decimal? Vvc2 { get; set; }
        public decimal? Vvc3 { get; set; }
        public short? ProcStatus { get; set; }
    }

    internal class SmithChartPointRecord
    {
        public long PointId { get; set; }
        public long StepId { get; set; }
        public string Channel { get; set; }
        public decimal? VoutVrms { get; set; }
        public decimal? IoutArms { get; set; }
        public decimal? PhaseDeg { get; set; }
        public decimal? ROhm { get; set; }
        public decimal? XOhm { get; set; }
        public decimal? GammaReal { get; set; }
        public decimal? GammaImag { get; set; }
        public decimal? GammaMag { get; set; }
        public decimal? Vswr { get; set; }
        public string ZText { get; set; }
        public string ZNormalized { get; set; }
        public decimal? ForwardPW { get; set; }
        public decimal? ReflectedPW { get; set; }
        public decimal? DeliveredPW { get; set; }
        public decimal? ReturnLossDb { get; set; }
        public decimal? EfficiencyPct { get; set; }
    }

    internal static class MeasurementDb
    {
        private const string ConnectionStringName = "MeasurementDb";

        public static NpgsqlConnection CreateConnection()
        {
            var connectionString = ConfigurationManager.ConnectionStrings[ConnectionStringName]?.ConnectionString;

            if (string.IsNullOrWhiteSpace(connectionString))
                throw new InvalidOperationException("App.config의 MeasurementDb 연결 문자열이 비어 있습니다.");

            return new NpgsqlConnection(connectionString);
        }

        public static double? GetActiveThreshold(string recipeName, string channel)
        {
            const string sql = @"
SELECT threshold FROM anomaly_threshold_config
WHERE recipe_name = @recipe_name AND channel::text = @channel;";

            using (var conn = CreateConnection())
            using (var cmd = new NpgsqlCommand(sql, conn))
            {
                cmd.Parameters.AddWithValue("recipe_name", recipeName);
                cmd.Parameters.AddWithValue("channel", channel);
                conn.Open();
                var result = cmd.ExecuteScalar();
                return result == null || result == DBNull.Value ? (double?)null : Convert.ToDouble(result);
            }
        }

        public static void SaveCalibratedThreshold(
            string recipeName, string channel, double threshold,
            double percentile, int sampleRunCount, List<long> goldenRunIds, string calibratedBy = null)
        {
            using (var conn = CreateConnection())
            {
                conn.Open();
                using (var tx = conn.BeginTransaction())
                {
                    // 1) 현재 threshold upsert
                    const string upsertSql = @"
INSERT INTO anomaly_threshold_config
    (recipe_name, channel, threshold, percentile, sample_run_count, calibrated_at, updated_at)
VALUES
    (@recipe_name, @channel::rf_channel, @threshold, @percentile, @sample_run_count, now(), now())
ON CONFLICT (recipe_name, channel)
DO UPDATE SET threshold = EXCLUDED.threshold, percentile = EXCLUDED.percentile,
              sample_run_count = EXCLUDED.sample_run_count, updated_at = now();";

                    using (var cmd = new NpgsqlCommand(upsertSql, conn, tx))
                    {
                        cmd.Parameters.AddWithValue("recipe_name", recipeName);
                        cmd.Parameters.AddWithValue("channel", channel);
                        cmd.Parameters.AddWithValue("threshold", threshold);
                        cmd.Parameters.AddWithValue("percentile", percentile);
                        cmd.Parameters.AddWithValue("sample_run_count", sampleRunCount);
                        cmd.ExecuteNonQuery();
                    }

                    // 2) 이력 기록 + calibration_id 획득
                    const string logSql = @"
INSERT INTO anomaly_threshold_calibration_log
    (recipe_name, channel, threshold, percentile, sample_run_count, calibrated_by)
VALUES
    (@recipe_name, @channel::rf_channel, @threshold, @percentile, @sample_run_count, @calibrated_by)
RETURNING calibration_id;";

                    long calibrationId;
                    using (var cmd = new NpgsqlCommand(logSql, conn, tx))
                    {
                        cmd.Parameters.AddWithValue("recipe_name", recipeName);
                        cmd.Parameters.AddWithValue("channel", channel);
                        cmd.Parameters.AddWithValue("threshold", threshold);
                        cmd.Parameters.AddWithValue("percentile", percentile);
                        cmd.Parameters.AddWithValue("sample_run_count", sampleRunCount);
                        cmd.Parameters.AddWithValue("calibrated_by", (object)calibratedBy ?? DBNull.Value);
                        calibrationId = (long)cmd.ExecuteScalar();
                    }

                    // 3) 사용된 골든 런들 매핑
                    const string mapSql = @"
INSERT INTO anomaly_threshold_calibration_run (calibration_id, run_id)
VALUES (@calibration_id, @run_id);";

                    foreach (var runId in goldenRunIds)
                    {
                        using (var cmd = new NpgsqlCommand(mapSql, conn, tx))
                        {
                            cmd.Parameters.AddWithValue("calibration_id", calibrationId);
                            cmd.Parameters.AddWithValue("run_id", runId);
                            cmd.ExecuteNonQuery();
                        }
                    }

                    tx.Commit();
                }
            }
        }

        /// <summary>
        /// 특정 run_id, channel(Source/Bias)에 대한 스미스 차트 포인트를 조회하여
        /// ImpedanceAnomalyDetector에서 바로 사용할 수 있는 ImpedanceStepData 리스트로 반환합니다.
        /// </summary>
        /// <param name="runId">process_run.run_id</param>
        /// <param name="channel">"source" 또는 "bias" 등 channel 값 (null이면 전체 채널)</param>
        public static List<ImpedanceStepData> GetImpedanceStepsByRunId(long runId, string channel = null)
        {
            var sql = @"
SELECT s.step_num,
       p.r_ohm, p.x_ohm, p.vout_vrms, p.iout_arms, p.vswr
FROM smith_chart_point p
INNER JOIN process_step s ON s.step_id = p.step_id
WHERE s.run_id = @run_id";

            if (!string.IsNullOrWhiteSpace(channel))
                sql += " AND p.channel::text = @channel";

            sql += " ORDER BY s.step_num ASC, p.point_id ASC;";

            var result = new List<ImpedanceStepData>();

            using (var conn = CreateConnection())
            using (var cmd = new NpgsqlCommand(sql, conn))
            {
                cmd.Parameters.AddWithValue("run_id", runId);
                if (!string.IsNullOrWhiteSpace(channel))
                    cmd.Parameters.AddWithValue("channel", channel);

                conn.Open();

                using (var reader = cmd.ExecuteReader())
                {
                    while (reader.Read())
                    {
                        result.Add(new ImpedanceStepData
                        {
                            Step = Convert.ToInt32(GetValue<short>(reader, "step_num")),
                            R = ToDouble(GetValue<decimal?>(reader, "r_ohm")),
                            X = ToDouble(GetValue<decimal?>(reader, "x_ohm")),
                            Vout = ToDouble(GetValue<decimal?>(reader, "vout_vrms")),
                            Iout = ToDouble(GetValue<decimal?>(reader, "iout_arms")),
                            VSWR = ToDouble(GetValue<decimal?>(reader, "vswr"))
                        });
                    }
                }
            }

            return result;
        }

        public static List<string> GetProcessRunNames(DateTime? startTime = null, DateTime? endTime = null)
        {
            var sql = @"
SELECT run_name
FROM process_run
WHERE 1 = 1";

            if (startTime.HasValue)
                sql += " AND started_at >= @start_time";

            if (endTime.HasValue)
                sql += " AND ended_at <= @end_time";

            sql += " ORDER BY created_at DESC, run_name ASC;";

            var result = new List<string>();

            using (var conn = CreateConnection())
            using (var cmd = new NpgsqlCommand(sql, conn))
            {
                if (startTime.HasValue)
                    cmd.Parameters.AddWithValue("start_time", startTime.Value);

                if (endTime.HasValue)
                    cmd.Parameters.AddWithValue("end_time", endTime.Value);

                conn.Open();

                using (var reader = cmd.ExecuteReader())
                {
                    while (reader.Read())
                    {
                        result.Add(GetString(reader, "run_name"));
                    }
                }
            }

            return result;
        }

        /// <summary>
        /// Recipe name(부분일치), Step, Power(전달전력), 기간(startTime~endTime) 조건으로
        /// process_run을 검색하여 조건에 맞는 run_name 목록을 반환합니다.
        /// </summary>
        /// <param name="recipeName">Recipe name 부분 검색어 (null/빈 값이면 전체 대상)</param>
        /// <param name="stepNum">특정 Step 번호로 제한 (null이면 전체 Step)</param>
        /// <param name="minPower">전달 전력(delivered_p_w) 하한 (null이면 제한 없음)</param>
        /// <param name="maxPower">전달 전력(delivered_p_w) 상한 (null이면 제한 없음)</param>
        /// <param name="startTime">started_at 하한 (null이면 제한 없음)</param>
        /// <param name="endTime">ended_at 상한 (null이면 제한 없음)</param>
        public static List<string> SearchProcessRunNames(
            string recipeName = null,
            short? stepNum = null,
            decimal? minPower = null,
            decimal? maxPower = null,
            DateTime? startTime = null,
            DateTime? endTime = null)
        {
            var sql = @"
SELECT DISTINCT r.run_name, r.created_at
FROM process_run r";

            // Step 또는 Power 조건이 있을 때만 process_step / smith_chart_point 조인
            var needsStepJoin = stepNum.HasValue || minPower.HasValue || maxPower.HasValue;

            if (needsStepJoin)
            {
                sql += @"
INNER JOIN process_step s ON s.run_id = r.run_id";

                if (minPower.HasValue || maxPower.HasValue)
                {
                    sql += @"
INNER JOIN smith_chart_point p ON p.step_id = s.step_id";
                }
            }

            sql += " WHERE 1 = 1";

            if (!string.IsNullOrWhiteSpace(recipeName))
                sql += " AND r.recipe_name ILIKE @recipe_name";

            if (startTime.HasValue)
                sql += " AND r.started_at >= @start_time";

            if (endTime.HasValue)
                sql += " AND r.ended_at <= @end_time";

            if (stepNum.HasValue)
                sql += " AND s.step_num = @step_num";

            if (minPower.HasValue)
                sql += " AND p.delivered_p_w >= @min_power";

            if (maxPower.HasValue)
                sql += " AND p.delivered_p_w <= @max_power";

            sql += " ORDER BY r.created_at DESC, r.run_name ASC;";

            var result = new List<string>();

            using (var conn = CreateConnection())
            using (var cmd = new NpgsqlCommand(sql, conn))
            {
                if (!string.IsNullOrWhiteSpace(recipeName))
                    cmd.Parameters.AddWithValue("recipe_name", $"%{recipeName}%");

                if (startTime.HasValue)
                    cmd.Parameters.AddWithValue("start_time", startTime.Value);

                if (endTime.HasValue)
                    cmd.Parameters.AddWithValue("end_time", endTime.Value);

                if (stepNum.HasValue)
                    cmd.Parameters.AddWithValue("step_num", stepNum.Value);

                if (minPower.HasValue)
                    cmd.Parameters.AddWithValue("min_power", minPower.Value);

                if (maxPower.HasValue)
                    cmd.Parameters.AddWithValue("max_power", maxPower.Value);

                conn.Open();

                using (var reader = cmd.ExecuteReader())
                {
                    while (reader.Read())
                    {
                        result.Add(GetString(reader, "run_name"));
                    }
                }
            }

            return result;
        }

        public static List<ProcessRunRecord> GetProcessRuns()
        {
            const string sql = @"
SELECT run_id, run_name, recipe_name, equipment_id, started_at, ended_at, created_at
FROM process_run
ORDER BY created_at DESC, run_name ASC;";

            var result = new List<ProcessRunRecord>();

            using (var conn = CreateConnection())
            using (var cmd = new NpgsqlCommand(sql, conn))
            {
                conn.Open();

                using (var reader = cmd.ExecuteReader())
                {
                    while (reader.Read())
                        result.Add(MapProcessRun(reader));
                }
            }

            return result;
        }

        public static ProcessRunRecord GetProcessRunById(long runId)
        {
            const string sql = @"
SELECT run_id, run_name, recipe_name, equipment_id, started_at, ended_at, created_at
FROM process_run
WHERE run_id = @run_id;";

            using (var conn = CreateConnection())
            using (var cmd = new NpgsqlCommand(sql, conn))
            {
                cmd.Parameters.AddWithValue("run_id", runId);
                conn.Open();

                using (var reader = cmd.ExecuteReader())
                {
                    return reader.Read() ? MapProcessRun(reader) : null;
                }
            }
        }

        public static ProcessRunRecord GetProcessRunByName(string runName)
        {
            const string sql = @"
SELECT run_id, run_name, recipe_name, equipment_id, started_at, ended_at, created_at
FROM process_run
WHERE run_name = @run_name;";

            using (var conn = CreateConnection())
            using (var cmd = new NpgsqlCommand(sql, conn))
            {
                cmd.Parameters.AddWithValue("run_name", runName ?? string.Empty);
                conn.Open();

                using (var reader = cmd.ExecuteReader())
                {
                    return reader.Read() ? MapProcessRun(reader) : null;
                }
            }
        }

        public static List<ProcessStepRecord> GetProcessStepsByRunId(long runId)
        {
            const string sql = @"
SELECT step_id, run_id, step_num, step_name, log_date, log_time,
       srf_freq, s_fwd, s_ref, s_vrms, s_irms, s_phase, s_delivered_pwr,
       s_preset_load, s_preset_tune, s_load_pos, s_tune_pos,
       br_freq, b_fwd, b_ref, b_vrms, b_irms, b_phase, b_delivered_pwr,
       b_preset_load, b_preset_tune, b_load_pos, b_tune_pos,
       ar_flow, o2_flow, apc_pressure, apc_position, vvc1, vvc2, vvc3, proc_status
FROM process_step
WHERE run_id = @run_id
ORDER BY step_num ASC;";

            var result = new List<ProcessStepRecord>();

            using (var conn = CreateConnection())
            using (var cmd = new NpgsqlCommand(sql, conn))
            {
                cmd.Parameters.AddWithValue("run_id", runId);
                conn.Open();

                using (var reader = cmd.ExecuteReader())
                {
                    while (reader.Read())
                        result.Add(MapProcessStep(reader));
                }
            }

            return result;
        }

        public static List<SmithChartPointRecord> GetSmithChartPointsByStepId(long stepId)
        {
            const string sql = @"
SELECT point_id, step_id, channel, vout_vrms, iout_arms, phase_deg,
       r_ohm, x_ohm, gamma_real, gamma_imag, gamma_mag, vswr,
       z_text, z_normalized, forward_p_w, reflected_p_w, delivered_p_w,
       return_loss_db, efficiency_pct
FROM smith_chart_point
WHERE step_id = @step_id
ORDER BY point_id ASC;";

            var result = new List<SmithChartPointRecord>();

            using (var conn = CreateConnection())
            using (var cmd = new NpgsqlCommand(sql, conn))
            {
                cmd.Parameters.AddWithValue("step_id", stepId);
                conn.Open();

                using (var reader = cmd.ExecuteReader())
                {
                    while (reader.Read())
                        result.Add(MapSmithChartPoint(reader));
                }
            }

            return result;
        }

        public static List<SmithChartPointRecord> GetSmithChartPointsByRunId(long runId, string channel = null)
        {
            var sql = @"
SELECT p.point_id, p.step_id, p.channel, p.vout_vrms, p.iout_arms, p.phase_deg,
       p.r_ohm, p.x_ohm, p.gamma_real, p.gamma_imag, p.gamma_mag, p.vswr,
       p.z_text, p.z_normalized, p.forward_p_w, p.reflected_p_w, p.delivered_p_w,
       p.return_loss_db, p.efficiency_pct
FROM smith_chart_point p
INNER JOIN process_step s ON s.step_id = p.step_id
WHERE s.run_id = @run_id";

            if (!string.IsNullOrWhiteSpace(channel))
                sql += " AND p.channel::text = @channel";

            sql += " ORDER BY s.step_num ASC, p.point_id ASC;";

            var result = new List<SmithChartPointRecord>();

            using (var conn = CreateConnection())
            using (var cmd = new NpgsqlCommand(sql, conn))
            {
                cmd.Parameters.AddWithValue("run_id", runId);
                if (!string.IsNullOrWhiteSpace(channel))
                    cmd.Parameters.AddWithValue("channel", channel);

                conn.Open();

                using (var reader = cmd.ExecuteReader())
                {
                    while (reader.Read())
                        result.Add(MapSmithChartPoint(reader));
                }
            }

            return result;
        }

        public static MeasurementDataset GetMeasurementDatasetByRunId(long runId, string channel, double z0 = 50.0, List<ProcessStepRecord> steps = null)
        {
            const string sql = @"
SELECT r.run_name,
       s.step_num,
       p.vout_vrms, p.iout_arms, p.phase_deg,
       p.r_ohm, p.x_ohm,
       p.gamma_real, p.gamma_imag, p.gamma_mag, p.vswr,
       p.z_text, p.z_normalized,
       p.forward_p_w, p.reflected_p_w, p.delivered_p_w
FROM process_run r
INNER JOIN process_step s ON s.run_id = r.run_id
INNER JOIN smith_chart_point p ON p.step_id = s.step_id
WHERE r.run_id = @run_id
  AND p.channel::text = @channel
ORDER BY s.step_num ASC;";

            MeasurementDataset ds = null;
            int i = 0;

            using (var conn = CreateConnection())
            using (var cmd = new NpgsqlCommand(sql, conn))
            {
                cmd.Parameters.AddWithValue("run_id", runId);
                cmd.Parameters.AddWithValue("channel", channel ?? string.Empty);
                conn.Open();

                using (var reader = cmd.ExecuteReader())
                {
                    while (reader.Read())
                    {
                        if (ds == null)
                        {
                            ds = new MeasurementDataset
                            {
                                Name = GetString(reader, "run_name") + "_" + channel,
                                Z0 = z0
                            };
                        }

                        ds.Steps.Add(new MeasurementStep
                        {
                            Step = Convert.ToInt32(GetValue<short>(reader, "step_num")),
                            Vout_Vrms = ToDouble(GetValue<decimal?>(reader, "vout_vrms")),
                            Iout_Arms = ToDouble(GetValue<decimal?>(reader, "iout_arms")),
                            Phase_deg = ToDouble(GetValue<decimal?>(reader, "phase_deg")),
                            R = ToDouble(GetValue<decimal?>(reader, "r_ohm")),
                            X = ToDouble(GetValue<decimal?>(reader, "x_ohm")),
                            Gamma_Real = ToDouble(GetValue<decimal?>(reader, "gamma_real")),
                            Gamma_Imag = ToDouble(GetValue<decimal?>(reader, "gamma_imag")),
                            VSWR = ToDouble(GetValue<decimal?>(reader, "vswr")),
                            Z_Text = GetString(reader, "z_text"),
                            Z_Normalized = GetString(reader, "z_normalized"),
                            ForwardP_W = ToDouble(GetValue<decimal?>(reader, "forward_p_w")),
                            ReflectedP_W = ToDouble(GetValue<decimal?>(reader, "reflected_p_w")),
                            DeliveredP_W = ToDouble(GetValue<decimal?>(reader, "delivered_p_w")),
                            Ar_Flow = ToDouble(steps[i].ArFlow),
                            O2_Flow = ToDouble(steps[i].O2Flow),
                            APC_Pressure = ToDouble(steps[i].ApcPressure),
                            APC_Position = ToDouble(steps[i].ApcPosition),
                            VVC1 = ToDouble(steps[i].Vvc1),
                            VVC2 = ToDouble(steps[i].Vvc2),
                            VVC3 = ToDouble(steps[i].Vvc3),
                            Proc_Status = steps[i].ProcStatus switch
                            {
                                null => string.Empty,
                                0 => "Process Run 정상",
                                1 => "Heavy alarm",
                                _ => "Unknown"
                            },

                        });

                        i++;
                    }
                }
            }

            return ds ?? new MeasurementDataset
            {
                Name = "EMPTY_" + channel,
                Z0 = z0
            };
        }

        private static ProcessRunRecord MapProcessRun(NpgsqlDataReader reader)
        {
            return new ProcessRunRecord
            {
                RunId = GetValue<long>(reader, "run_id"),
                RunName = GetString(reader, "run_name"),
                RecipeName = GetString(reader, "recipe_name"),
                EquipmentId = GetString(reader, "equipment_id"),
                StartedAt = GetValue<DateTime?>(reader, "started_at"),
                EndedAt = GetValue<DateTime?>(reader, "ended_at"),
                CreatedAt = GetValue<DateTime?>(reader, "created_at")
            };
        }

        private static ProcessStepRecord MapProcessStep(NpgsqlDataReader reader)
        {
            return new ProcessStepRecord
            {
                StepId = GetValue<long>(reader, "step_id"),
                RunId = GetValue<long>(reader, "run_id"),
                StepNum = GetValue<short>(reader, "step_num"),
                StepName = GetString(reader, "step_name"),
                LogDate = GetValue<DateTime?>(reader, "log_date"),
                LogTime = GetValue<TimeSpan?>(reader, "log_time"),
                SrfFreq = GetValue<decimal?>(reader, "srf_freq"),
                SFwd = GetValue<decimal?>(reader, "s_fwd"),
                SRef = GetValue<decimal?>(reader, "s_ref"),
                SVrms = GetValue<decimal?>(reader, "s_vrms"),
                SIrms = GetValue<decimal?>(reader, "s_irms"),
                SPhase = GetValue<decimal?>(reader, "s_phase"),
                SDeliveredPwr = GetValue<decimal?>(reader, "s_delivered_pwr"),
                SPresetLoad = GetValue<decimal?>(reader, "s_preset_load"),
                SPresetTune = GetValue<decimal?>(reader, "s_preset_tune"),
                SLoadPos = GetValue<decimal?>(reader, "s_load_pos"),
                STunePos = GetValue<decimal?>(reader, "s_tune_pos"),
                BrfFreq = GetValue<decimal?>(reader, "br_freq"),
                BFwd = GetValue<decimal?>(reader, "b_fwd"),
                BRef = GetValue<decimal?>(reader, "b_ref"),
                BVrms = GetValue<decimal?>(reader, "b_vrms"),
                BIrms = GetValue<decimal?>(reader, "b_irms"),
                BPhase = GetValue<decimal?>(reader, "b_phase"),
                BDeliveredPwr = GetValue<decimal?>(reader, "b_delivered_pwr"),
                BPresetLoad = GetValue<decimal?>(reader, "b_preset_load"),
                BPresetTune = GetValue<decimal?>(reader, "b_preset_tune"),
                BLoadPos = GetValue<decimal?>(reader, "b_load_pos"),
                BTunePos = GetValue<decimal?>(reader, "b_tune_pos"),
                ArFlow = GetValue<decimal?>(reader, "ar_flow"),
                O2Flow = GetValue<decimal?>(reader, "o2_flow"),
                ApcPressure = GetValue<decimal?>(reader, "apc_pressure"),
                ApcPosition = GetValue<decimal?>(reader, "apc_position"),
                Vvc1 = GetValue<decimal?>(reader, "vvc1"),
                Vvc2 = GetValue<decimal?>(reader, "vvc2"),
                Vvc3 = GetValue<decimal?>(reader, "vvc3"),
                ProcStatus = GetValue<short?>(reader, "proc_status")
            };
        }

        private static SmithChartPointRecord MapSmithChartPoint(NpgsqlDataReader reader)
        {
            return new SmithChartPointRecord
            {
                PointId = GetValue<long>(reader, "point_id"),
                StepId = GetValue<long>(reader, "step_id"),
                Channel = GetString(reader, "channel"),
                VoutVrms = GetValue<decimal?>(reader, "vout_vrms"),
                IoutArms = GetValue<decimal?>(reader, "iout_arms"),
                PhaseDeg = GetValue<decimal?>(reader, "phase_deg"),
                ROhm = GetValue<decimal?>(reader, "r_ohm"),
                XOhm = GetValue<decimal?>(reader, "x_ohm"),
                GammaReal = GetValue<decimal?>(reader, "gamma_real"),
                GammaImag = GetValue<decimal?>(reader, "gamma_imag"),
                GammaMag = GetValue<decimal?>(reader, "gamma_mag"),
                Vswr = GetValue<decimal?>(reader, "vswr"),
                ZText = GetString(reader, "z_text"),
                ZNormalized = GetString(reader, "z_normalized"),
                ForwardPW = GetValue<decimal?>(reader, "forward_p_w"),
                ReflectedPW = GetValue<decimal?>(reader, "reflected_p_w"),
                DeliveredPW = GetValue<decimal?>(reader, "delivered_p_w"),
                ReturnLossDb = GetValue<decimal?>(reader, "return_loss_db"),
                EfficiencyPct = GetValue<decimal?>(reader, "efficiency_pct")
            };
        }

        private static T GetValue<T>(NpgsqlDataReader reader, string columnName)
        {
            var ordinal = reader.GetOrdinal(columnName);
            if (reader.IsDBNull(ordinal))
                return default(T);

            return (T)reader.GetValue(ordinal);
        }

        private static string GetString(NpgsqlDataReader reader, string columnName)
        {
            var value = GetValue<object>(reader, columnName);
            return value == null ? string.Empty : Convert.ToString(value, CultureInfo.InvariantCulture);
        }

        private static double ToDouble(decimal? value)
        {
            return value.HasValue ? Convert.ToDouble(value.Value) : 0d;
        }
    }
}