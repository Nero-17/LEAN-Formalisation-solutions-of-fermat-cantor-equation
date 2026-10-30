import LambdaCantor.RationalPowers.LargeExponentCachedChecks

namespace LambdaCantor.RationalPowers
open Integer

structure CertifiedLargeExponentCachedBlock where
  context : FinitePhaseCell
  table : LargeExponentCachedTable
  cells : List LargeExponentCachedCell
  table_checked : table.check context = true
  cells_checked : largeExponentCachedCellsCheck context table cells = true

/-- The final coverage computation inspects only exact coefficient intervals
and denominator identifiers. Each selected interval retains its own block,
context, accepted source table and independently accepted phase arcs. -/
def largeExponentCachedCoverageRows (blocks : List CertifiedLargeExponentCachedBlock)
    (denominator : ℕ) : List FiniteCoverageRow :=
  (((blocks.flatMap (fun block => block.cells)).filter
    (fun cell => decide (cell.denominator = denominator))).map LargeExponentCachedCell.interval).mergeSort
      (fun first second => decide (first.cell.lower*first.multiplier ≤ second.cell.lower*second.multiplier))

def largeExponentCachedBlocksCoverCheck (layer commonDenominator : ℕ)
    (denominators : List ℕ) (blocks : List CertifiedLargeExponentCachedBlock) : Bool :=
  denominators.all (fun denominator => finiteCoverageCheck layer commonDenominator
    (largeExponentCachedCoverageRows blocks denominator))

end LambdaCantor.RationalPowers
