import LambdaCantor.Integer.FinitePhaseChecker

namespace LambdaCantor.Integer

/-- A common integer grid for the outer coefficient cover. The multiplier is
checked exactly, so no rounding weakens the individual cell bounds. -/
structure FiniteCoverageRow where
  cell : FinitePhaseCell
  multiplier : ℕ
  deriving Inhabited

def finiteCoverageIntervals (rows : List FiniteCoverageRow) : List (ℤ × ℤ) :=
  rows.map (fun row => (row.cell.lower*row.multiplier,row.cell.upper*row.multiplier))

def finiteCoverageCheck (m denominator : ℕ) (rows : List FiniteCoverageRow) : Bool :=
  decide (0 < denominator) &&
  rows.all (fun row => decide (row.cell.m = m ∧ 0 < row.multiplier ∧
    row.cell.denominator*row.multiplier = denominator)) &&
  intervalCoverScan (finiteCoverageIntervals rows) denominator (3*denominator) &&
  rows.any (fun row => decide (row.cell.lower*row.multiplier ≤ denominator ∧
    denominator ≤ row.cell.upper*row.multiplier))

end LambdaCantor.Integer
