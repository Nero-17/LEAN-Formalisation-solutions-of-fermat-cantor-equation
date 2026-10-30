import LambdaCantor.RationalPowers.LargeExponentRawPhaseCore

namespace LambdaCantor.RationalPowers.RawPhase

structure CachedCell where
  cell : Cell
  multiplier : Nat
  denominator : Nat
  arcs : List Arc

structure Block where
  context : Cell
  sources : Array Geometry
  caches : Array Cache
  cells : List CachedCell

def sameContext (first second : Cell) : Prop :=
  first.m = second.m ∧ first.endpointDepth = second.endpointDepth ∧
  first.height = second.height ∧ first.verticalDepth = second.verticalDepth ∧
  first.endpoint = second.endpoint

instance (first second : Cell) : Decidable (sameContext first second) := by
  unfold sameContext
  infer_instance

def cellsCheck (context : Cell) (sources : Array Geometry) (caches : Array Cache)
    (cells : List CachedCell) : Bool :=
  cells.all (fun entry =>
    decide (0 < entry.denominator ∧ entry.cell.Checked ∧ sameContext context entry.cell) &&
      coreCheck entry.denominator entry.cell sources caches entry.arcs)

def CachedCell.gridRow (entry : CachedCell) : CheapGrid.Row :=
  ⟨entry.cell.m,entry.cell.denominator,entry.cell.lower,entry.cell.upper,entry.multiplier⟩

def coverageRows (blocks : List Block) (denominator : Nat) : List CheapGrid.Row :=
  (((blocks.flatMap Block.cells).filter
    (fun entry => decide (entry.denominator = denominator))).map CachedCell.gridRow).mergeSort
      (fun first second => decide (first.lower*first.multiplier ≤ second.lower*second.multiplier))

def blocksCoverCheck (layer commonDenominator : Nat) (denominators : List Nat)
    (blocks : List Block) : Bool :=
  denominators.all (fun denominator => CheapGrid.cover layer commonDenominator
    (coverageRows blocks denominator).toArray)

end LambdaCantor.RationalPowers.RawPhase
