import LambdaCantor.RationalPowers.LargeExponentRawPhaseCore
import LambdaCantor.RationalPowers.LargeExponentCheapGridBridge
import LambdaCantor.RationalPowers.LargeExponentCachedChecks
import Mathlib.Tactic.FinCases

namespace LambdaCantor.RationalPowers
open Integer

def RawPhase.Cell.toCell (cell : RawPhase.Cell) : FinitePhaseCell :=
  ⟨cell.m,cell.endpointDepth,cell.height,cell.verticalDepth,cell.endpoint,
    cell.denominator,cell.lower,cell.upper⟩

def RawPhase.Geometry.toGeometry (geometry : RawPhase.Geometry) : TailPhaseGeometry :=
  ⟨geometry.p,geometry.q,geometry.a⟩

def RawPhase.Interval.toInterval (interval : RawPhase.Interval) : IntInterval :=
  ⟨interval.lower,interval.upper⟩

def RawPhase.Cache.toCache (cache : RawPhase.Cache) : TailPhaseCache :=
  ⟨cache.qLog.toInterval,cache.nextQLog.toInterval,cache.atOffset.toInterval,cache.atNextOffset.toInterval⟩

def RawPhase.Arc.toArc (arc : RawPhase.Arc) : FinitePhaseArc :=
  ⟨arc.sourceIndex,arc.shift,arc.band⟩

theorem largeExponent_raw_decode_eq (encoded : Nat) :
    (RawPhase.decodeArc encoded).toArc = decodeLargeExponentCachedArc encoded := by rfl

theorem largeExponent_raw_ternary_prefix_eq (word depth : Nat) :
    RawPhase.ternaryPrefix word depth = ternaryPrefix word depth := by
  induction depth generalizing word with
  | zero => rfl
  | succ depth induction_hypothesis =>
    simp only [RawPhase.ternaryPrefix,ternaryPrefix,induction_hypothesis]

theorem largeExponent_raw_cell_checked_eq (cell : RawPhase.Cell) :
    cell.Checked = cell.toCell.Checked := by
  simp only [RawPhase.Cell.Checked,FinitePhaseCell.Checked,RawPhase.Cell.toCell,
    largeExponent_raw_ternary_prefix_eq]

theorem largeExponent_raw_band_eq (band : Fin 14) :
    RawPhase.band band = finitePhaseBand band := by
  fin_cases band <;> rfl

theorem largeExponent_raw_geometry_checked_eq
    (cell : RawPhase.Cell) (geometry : RawPhase.Geometry) (band : Fin 14) :
    RawPhase.geometryChecked cell geometry band =
      finitePhaseGeometryChecked cell.toCell geometry.toGeometry band := by
  simp only [RawPhase.geometryChecked,finitePhaseGeometryChecked,RawPhase.Cell.toCell,
    RawPhase.Geometry.toGeometry,RawPhase.center,finitePhaseCenter,RawPhase.length,finitePhaseLength,
    largeExponent_raw_band_eq,largeExponent_raw_ternary_prefix_eq]

theorem largeExponent_raw_map_getElem! {α β : Type*} [Inhabited α] [Inhabited β]
    (mapping : α → β) (default_identity : mapping default = default) (values : Array α) (index : Nat) :
    (values.map mapping)[index]! = mapping values[index]! := by
  by_cases bound : index < values.size
  · rw [getElem!_pos (values.map mapping) index (by simpa only [Array.size_map] using bound),
      getElem!_pos values index bound]
    exact Array.getElem_map mapping _
  · rw [getElem!_neg (values.map mapping) index (by simpa only [Array.size_map] using bound),
      getElem!_neg values index bound]
    exact default_identity.symm

theorem largeExponent_raw_phase_interval_eq (denominator : Nat) (cell : RawPhase.Cell)
    (cache : RawPhase.Cache) (arc : RawPhase.Arc) :
    RawPhase.phaseInterval denominator cell cache arc =
      ((largeExponentGroupedPhaseRow denominator cell.toCell cache.toCache arc.toArc).lower,
       (largeExponentGroupedPhaseRow denominator cell.toCell cache.toCache arc.toArc).upper) := by
  rfl

/-- Exact equality to the frozen denominator-aware core, including lookup
defaults, the fourteen bands, strict geometry, clipping and signed rotation.
The raw native computation never evaluates a logarithm. -/
theorem largeExponent_raw_phase_core_eq (denominator : Nat) (cell : RawPhase.Cell)
    (sources : Array RawPhase.Geometry) (caches : Array RawPhase.Cache) (arcs : List RawPhase.Arc) :
    RawPhase.coreCheck denominator cell sources caches arcs =
      largeExponentGroupedCellCoreCheck denominator cell.toCell
        (sources.map RawPhase.Geometry.toGeometry) (caches.map RawPhase.Cache.toCache)
        (arcs.map RawPhase.Arc.toArc) := by
  have geometry_lookup (index : Nat) :
      (sources.map RawPhase.Geometry.toGeometry)[index]! = sources[index]!.toGeometry :=
    largeExponent_raw_map_getElem! RawPhase.Geometry.toGeometry rfl sources index
  have cache_lookup (index : Nat) :
      (caches.map RawPhase.Cache.toCache)[index]! = caches[index]!.toCache :=
    largeExponent_raw_map_getElem! RawPhase.Cache.toCache rfl caches index
  let convertedRow (arc : RawPhase.Arc) : PhaseCoverRow :=
    largeExponentGroupedPhaseRow denominator cell.toCell
      (caches.map RawPhase.Cache.toCache)[arc.toArc.sourceIndex]! arc.toArc
  have geometry_predicate :
      (fun arc : RawPhase.Arc => decide (arc.sourceIndex < sources.size ∧
        RawPhase.geometryChecked cell sources[arc.sourceIndex]! arc.band)) =
      (fun arc : RawPhase.Arc => decide (arc.toArc.sourceIndex <
        (sources.map RawPhase.Geometry.toGeometry).size ∧
        finitePhaseGeometryChecked cell.toCell
          (sources.map RawPhase.Geometry.toGeometry)[arc.toArc.sourceIndex]! arc.toArc.band)) := by
    funext arc
    apply decide_eq_decide.mpr
    simp only [RawPhase.Arc.toArc,Array.size_map,geometry_lookup,
      largeExponent_raw_geometry_checked_eq]
  have phase_interval (arc : RawPhase.Arc) :
      RawPhase.phaseInterval denominator cell caches[arc.sourceIndex]! arc =
        ((convertedRow arc).lower,(convertedRow arc).upper) := by
    simpa only [convertedRow,RawPhase.Arc.toArc,cache_lookup] using
      largeExponent_raw_phase_interval_eq denominator cell caches[arc.sourceIndex]! arc
  have interval_functions :
      (fun arc : RawPhase.Arc => RawPhase.phaseInterval denominator cell caches[arc.sourceIndex]! arc) =
      (fun arc : RawPhase.Arc => ((convertedRow arc).lower,(convertedRow arc).upper)) := by
    funext arc
    exact phase_interval arc
  have initial_predicate :
      (fun arc : RawPhase.Arc => decide
        ((RawPhase.phaseInterval denominator cell caches[arc.sourceIndex]! arc).1 ≤ 0 ∧
          0 ≤ (RawPhase.phaseInterval denominator cell caches[arc.sourceIndex]! arc).2)) =
      (fun arc : RawPhase.Arc => decide ((convertedRow arc).lower ≤ 0 ∧
        0 ≤ (convertedRow arc).upper)) := by
    funext arc
    apply decide_eq_decide.mpr
    simp only [phase_interval arc]
  have scale_identity : (cell.denominator : Int)*2^80 =
      ((cell.toCell.denominator*2^80 : Nat) : Int) := by
    simp only [RawPhase.Cell.toCell,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have phase_scan :
      CheapGrid.intervalScan
          (arcs.map (fun arc => RawPhase.phaseInterval denominator cell caches[arc.sourceIndex]! arc))
          0 ((cell.denominator : Int)*2^80) =
        intervalCoverScan (arcs.map (fun arc => ((convertedRow arc).lower,(convertedRow arc).upper)))
          0 (cell.toCell.denominator*2^80 : Nat) := by
    rw [largeExponent_cheap_interval_scan_eq,interval_functions,scale_identity]
  have geometry_all := congrArg (fun predicate => arcs.all predicate) geometry_predicate
  have phase_initial := congrArg (fun predicate => arcs.any predicate) initial_predicate
  have core_identity := congrArg₂ Bool.and geometry_all (congrArg₂ Bool.and phase_scan phase_initial)
  simpa only [RawPhase.coreCheck,largeExponentGroupedCellCoreCheck,phaseCoverCheck,
    List.all_map,List.any_map,List.map_map,Function.comp_def,convertedRow] using core_identity

#print axioms largeExponent_raw_phase_core_eq

end LambdaCantor.RationalPowers
