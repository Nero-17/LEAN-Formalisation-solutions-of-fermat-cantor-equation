import LambdaCantor.Integer.FinitePhaseChecker

namespace LambdaCantor.RationalPowers
open Integer

def largeExponentGroupedPhaseRow (denominator : ℕ) (cell : FinitePhaseCell)
    (cache : TailPhaseCache) (arc : FinitePhaseArc) : PhaseCoverRow :=
  { sourceIndex := arc.sourceIndex
    lower := max 0 ((denominator : ℤ)*finitePhaseLower cell cache-arc.shift*(cell.denominator*2^80))
    upper := min (cell.denominator*2^80)
      ((denominator : ℤ)*finitePhaseUpper cell cache-arc.shift*(cell.denominator*2^80))
    shift := arc.shift }

def largeExponentGroupedCellCoreCheck (denominator : ℕ) (cell : FinitePhaseCell)
    (sources : Array TailPhaseGeometry) (caches : Array TailPhaseCache)
    (arcs : List FinitePhaseArc) : Bool :=
  arcs.all (fun arc => decide (arc.sourceIndex < sources.size ∧
    finitePhaseGeometryChecked cell sources[arc.sourceIndex]! arc.band)) &&
  phaseCoverCheck (cell.denominator*2^80) (arcs.map (fun arc =>
    largeExponentGroupedPhaseRow denominator cell caches[arc.sourceIndex]! arc))

/-- Each invocation has one cell and therefore exactly one endpoint/center.
The caller selects that cell separately for the given reduced denominator. -/
def largeExponentGroupedCellCheck (denominator : ℕ) (cell : FinitePhaseCell)
    (sources : Array TailPhaseGeometry) (arcs : List FinitePhaseArc) : Bool :=
  decide (0 < denominator ∧ cell.Checked) &&
  sources.all (fun geometry => decide (finitePhaseAnalyticChecked cell geometry)) &&
  largeExponentGroupedCellCoreCheck denominator cell sources (sources.map (finitePhaseCache cell)) arcs

structure LargeExponentGroupedBatchItem where
  denominator : ℕ
  arcs : List FinitePhaseArc

def largeExponentGroupedBatchCheck (cell : FinitePhaseCell) (sources : Array TailPhaseGeometry)
    (items : List LargeExponentGroupedBatchItem) : Bool :=
  let caches := sources.map (finitePhaseCache cell)
  decide cell.Checked &&
  sources.all (fun geometry => decide (finitePhaseAnalyticChecked cell geometry)) &&
  items.all (fun item => decide (0 < item.denominator) &&
    largeExponentGroupedCellCoreCheck item.denominator cell sources caches item.arcs)

/-- Scaling raw phase intervals by one is exactly the original continuous
full-phase checker, including its clipping and integer rotations. -/
theorem largeExponent_grouped_one_check (cell : FinitePhaseCell)
    (sources : Array TailPhaseGeometry) (arcs : List FinitePhaseArc) :
    largeExponentGroupedCellCheck 1 cell sources arcs = finitePhaseCellCheck cell sources arcs := by
  have rows : ∀ cache arc, largeExponentGroupedPhaseRow 1 cell cache arc = finitePhaseRow cell cache arc := by
    intro cache arc
    simp only [largeExponentGroupedPhaseRow,finitePhaseRow,Nat.cast_one,one_mul]
  simp only [largeExponentGroupedCellCheck,largeExponentGroupedCellCoreCheck,finitePhaseCellCheck,
    rows,Nat.zero_lt_one,true_and,Bool.and_assoc]

end LambdaCantor.RationalPowers
