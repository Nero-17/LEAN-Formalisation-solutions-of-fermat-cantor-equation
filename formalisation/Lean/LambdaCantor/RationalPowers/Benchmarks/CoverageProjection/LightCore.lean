import LambdaCantor.RationalPowers.LargeExponentCheapGrid

namespace LambdaCantor.RationalPowers.Benchmarks.CoverageProjection

/-- The first natural filters entry.denominator; the Row retains cell.denominator. -/
def coverageRows (entries : List (Nat × CheapGrid.Row)) (denominator : Nat) : List CheapGrid.Row :=
  ((entries.filter (fun entry => decide (entry.1 = denominator))).map Prod.snd).mergeSort
    (fun first second => decide (first.lower*first.multiplier ≤ second.lower*second.multiplier))

/-- Exactly the original sort and grid cover, operating on six retained fields. -/
def blocksCoverCheck (layer commonDenominator : Nat) (denominators : List Nat)
    (entries : List (Nat × CheapGrid.Row)) : Bool :=
  denominators.all (fun denominator => CheapGrid.cover layer commonDenominator
    (coverageRows entries denominator).toArray)

end LambdaCantor.RationalPowers.Benchmarks.CoverageProjection
