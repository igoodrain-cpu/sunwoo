namespace MeasurementImporterService.Models;

public enum RfChannel
{
    Source,
    Bias
}

/// <summary>
/// PROCESS_RUN + PROCESS_STEP + SMITH_CHART_POINT 적재를 위한 파일 단위 배치 모델.
/// </summary>
public sealed class MeasurementBatch
{
    public required Guid BatchId { get; init; }
    public required string SourceFile { get; init; }
    public required string FileHash { get; init; }
    public required string RunName { get; init; }
    public string? RecipeName { get; init; }
    public string? EquipmentId { get; init; }
    public required DateTime StartedAt { get; init; }
    public required DateTime EndedAt { get; init; }
    public required IReadOnlyList<ProcessStepRecord> Steps { get; init; }
}

public sealed class ProcessStepRecord
{
    public short StepNum { get; init; }
    public required string StepName { get; init; }
    public required DateOnly LogDate { get; init; }
    public required TimeOnly LogTime { get; init; }
    public decimal? SrfFreq { get; init; }
    public decimal? SFwd { get; init; }
    public decimal? SRef { get; init; }
    public decimal? SVrms { get; init; }
    public decimal? SIrms { get; init; }
    public decimal? SPhase { get; init; }
    public decimal? SDeliveredPwr { get; init; }
    public decimal? SPresetLoad { get; init; }
    public decimal? SPresetTune { get; init; }
    public decimal? SLoadPos { get; init; }
    public decimal? STunePos { get; init; }
    public decimal? BrFreq { get; init; }
    public decimal? BFwd { get; init; }
    public decimal? BRef { get; init; }
    public decimal? BVrms { get; init; }
    public decimal? BIrms { get; init; }
    public decimal? BPhase { get; init; }
    public decimal? BDeliveredPwr { get; init; }
    public decimal? BPresetLoad { get; init; }
    public decimal? BPresetTune { get; init; }
    public decimal? BLoadPos { get; init; }
    public decimal? BTunePos { get; init; }
    public decimal? ArFlow { get; init; }
    public decimal? O2Flow { get; init; }
    public decimal? ApcPressure { get; init; }
    public decimal? ApcPosition { get; init; }
    public decimal? Vvc1 { get; init; }
    public decimal? Vvc2 { get; init; }
    public decimal? Vvc3 { get; init; }
    public short ProcStatus { get; init; }
    public required SmithChartPointRecord SourcePoint { get; init; }
    public required SmithChartPointRecord BiasPoint { get; init; }
}

public sealed class SmithChartPointRecord
{
    public required RfChannel Channel { get; init; }
    public decimal? VoutVrms { get; init; }
    public decimal? IoutArms { get; init; }
    public decimal? PhaseDeg { get; init; }
    public decimal? ROhm { get; init; }
    public decimal? XOhm { get; init; }
    public decimal? GammaReal { get; init; }
    public decimal? GammaImag { get; init; }
    public decimal? GammaMag { get; init; }
    public decimal? Vswr { get; init; }
    public string? ZText { get; init; }
    public string? ZNormalized { get; init; }
    public decimal? ForwardPowerW { get; init; }
    public decimal? ReflectedPowerW { get; init; }
    public decimal? DeliveredPowerW { get; init; }
    public decimal? ReturnLossDb { get; init; }
    public decimal? EfficiencyPct { get; init; }

    public bool HasValues =>
        VoutVrms.HasValue ||
        IoutArms.HasValue ||
        PhaseDeg.HasValue ||
        ROhm.HasValue ||
        XOhm.HasValue ||
        GammaReal.HasValue ||
        GammaImag.HasValue ||
        GammaMag.HasValue ||
        Vswr.HasValue ||
        !string.IsNullOrWhiteSpace(ZText) ||
        !string.IsNullOrWhiteSpace(ZNormalized) ||
        ForwardPowerW.HasValue ||
        ReflectedPowerW.HasValue ||
        DeliveredPowerW.HasValue ||
        ReturnLossDb.HasValue ||
        EfficiencyPct.HasValue;
}
