import LambdaCantor.RationalPowers.LargeExponentRawLogArithmeticBridge

namespace LambdaCantor.RationalPowers

/-- Preserve every integer endpoint of the original offset computation. -/
theorem largeExponent_raw_log_offset_interval_eq
    (cell : RawPhase.Cell) (geometry : RawPhase.Geometry) (offset : Nat) :
    (RawLog.finitePhaseOffsetInterval cell geometry offset).toInterval =
      Integer.finitePhaseOffsetInterval cell.toCell geometry.toGeometry offset := by
  simpa only [RawLog.finitePhaseOffsetInterval,Integer.finitePhaseOffsetInterval,
    RawPhase.center,RawPhase.length,Integer.finitePhaseCenter,Integer.finitePhaseLength,
    RawPhase.Cell.toCell,RawPhase.Geometry.toGeometry] using
      largeExponent_raw_log_ratio_interval_eq (2^256) (2^80*3^cell.m)
        (2*RawPhase.center cell*RawPhase.length cell geometry+
          3^cell.height*RawPhase.length cell geometry)
        (2*RawPhase.center cell*RawPhase.length cell geometry+2*offset) 12

/-- Four intervals, all eight endpoints, in their original order. -/
theorem largeExponent_raw_log_cache_eq
    (cell : RawPhase.Cell) (geometry : RawPhase.Geometry) :
    (RawLog.finitePhaseCache cell geometry).toCache =
      Integer.finitePhaseCache cell.toCell geometry.toGeometry := by
  simp only [RawLog.finitePhaseCache,Integer.finitePhaseCache,RawPhase.Cache.toCache,
    largeExponent_raw_log_ratio_interval_eq,largeExponent_raw_log_offset_interval_eq,
    RawPhase.Cell.toCell,RawPhase.Geometry.toGeometry]

/-- The full analytic guard, including the fixed log-three denominator guard. -/
theorem largeExponent_raw_log_analytic_checked_eq
    (cell : RawPhase.Cell) (geometry : RawPhase.Geometry) :
    RawLog.finitePhaseAnalyticChecked cell geometry =
      Integer.finitePhaseAnalyticChecked cell.toCell geometry.toGeometry := by
  simp only [RawLog.finitePhaseAnalyticChecked,Integer.finitePhaseAnalyticChecked,
    largeExponent_raw_log_ratio_checked_eq,RawPhase.center,RawPhase.length,
    Integer.finitePhaseCenter,Integer.finitePhaseLength,
    RawPhase.Cell.toCell,RawPhase.Geometry.toGeometry]

/-- The conversion is injective on complete caches, not merely on their sizes. -/
theorem largeExponent_raw_log_cache_conversion_injective :
    Function.Injective RawPhase.Cache.toCache := by
  intro first second equal
  exact congrArg (fun cache : Integer.TailPhaseCache =>
    (⟨⟨cache.qLog.lower,cache.qLog.upper⟩,
      ⟨cache.nextQLog.lower,cache.nextQLog.upper⟩,
      ⟨cache.atOffset.lower,cache.atOffset.upper⟩,
      ⟨cache.atNextOffset.lower,cache.atNextOffset.upper⟩⟩ : RawPhase.Cache)) equal

/-- Convert supplied source and cache arrays without reordering or recomputing them. -/
def RawLog.toTable (sources : Array RawPhase.Geometry)
    (caches : Array RawPhase.Cache) : LargeExponentCachedTable :=
  ⟨sources.map RawPhase.Geometry.toGeometry,caches.map RawPhase.Cache.toCache⟩

/-- Exact Boolean equality with the original table predicate for arbitrary inputs.
No geometry, positivity, cache correctness, cell validity or phase-cover premise
is assumed. The supplied cache array is compared in full to recomputed intervals. -/
theorem largeExponent_raw_log_table_check_eq
    (cell : RawPhase.Cell) (sources : Array RawPhase.Geometry)
    (caches : Array RawPhase.Cache) :
    RawLog.tableCheck cell sources caches =
      (RawLog.toTable sources caches).check cell.toCell := by
  have analytic_identity :
      (sources.map RawPhase.Geometry.toGeometry).all
          (fun geometry => decide (Integer.finitePhaseAnalyticChecked cell.toCell geometry)) =
        sources.all (fun geometry => decide (RawLog.finitePhaseAnalyticChecked cell geometry)) := by
    simp only [Array.all_map,Function.comp_def,← largeExponent_raw_log_analytic_checked_eq]
  have cache_identity :
      (sources.map RawPhase.Geometry.toGeometry).map (Integer.finitePhaseCache cell.toCell) =
        (sources.map (RawLog.finitePhaseCache cell)).map RawPhase.Cache.toCache := by
    simp only [Array.map_map,Function.comp_def,largeExponent_raw_log_cache_eq]
  have cache_equality_identity :
      (caches.map RawPhase.Cache.toCache =
        (sources.map (RawLog.finitePhaseCache cell)).map RawPhase.Cache.toCache) =
      (caches = sources.map (RawLog.finitePhaseCache cell)) := by
    exact propext (Array.map_inj_right largeExponent_raw_log_cache_conversion_injective)
  simp only [RawLog.tableCheck,RawLog.toTable,LargeExponentCachedTable.check,
    analytic_identity,cache_identity,cache_equality_identity]

#print axioms largeExponent_raw_log_table_check_eq

end LambdaCantor.RationalPowers
