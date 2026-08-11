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
