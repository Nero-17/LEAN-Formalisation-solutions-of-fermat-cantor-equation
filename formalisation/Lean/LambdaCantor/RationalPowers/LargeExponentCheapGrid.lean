import Std

namespace LambdaCantor.RationalPowers.CheapGrid

/-- Only the five fields used by the outer coefficient-grid computation. -/
structure Row where
  layer : Nat
  denominator : Nat
  lower : Nat
  upper : Nat
  multiplier : Nat

def intervalScan : List (Int × Int) → Int → Int → Bool
  | [], frontier, target => decide (target ≤ frontier)
  | (lower,upper)::rest, frontier, target =>
      decide (lower ≤ frontier) && intervalScan rest (max frontier upper) target

def intervals (rows : Array Row) : List (Int × Int) :=
  rows.toList.map (fun row => (row.lower*row.multiplier,row.upper*row.multiplier))

def cover (layer denominator : Nat) (rows : Array Row) : Bool :=
  decide (0 < denominator) &&
  rows.toList.all (fun row => decide (row.layer = layer ∧ 0 < row.multiplier ∧
    row.denominator*row.multiplier = denominator)) &&
  intervalScan (intervals rows) denominator (3*denominator) &&
  rows.toList.any (fun row => decide (row.lower*row.multiplier ≤ denominator ∧
    denominator ≤ row.upper*row.multiplier))

end LambdaCantor.RationalPowers.CheapGrid
