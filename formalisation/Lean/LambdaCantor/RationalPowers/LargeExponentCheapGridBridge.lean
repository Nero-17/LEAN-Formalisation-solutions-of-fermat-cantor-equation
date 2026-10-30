import LambdaCantor.RationalPowers.LargeExponentCheapGrid
import LambdaCantor.Integer.FiniteCoverageChecks

namespace LambdaCantor.RationalPowers
open Integer

def largeExponentCheapGridRows (rows : List FiniteCoverageRow) : Array CheapGrid.Row :=
  (rows.map (fun row => ⟨row.cell.m,row.cell.denominator,row.cell.lower,row.cell.upper,row.multiplier⟩)).toArray

theorem largeExponent_cheap_interval_scan_eq (intervals : List (Int × Int)) (frontier target : Int) :
    CheapGrid.intervalScan intervals frontier target = intervalCoverScan intervals frontier target := by
  induction intervals generalizing frontier with
  | nil => rfl
  | cons interval rest induction_hypothesis =>
    rcases interval with ⟨lower,upper⟩
    simp only [CheapGrid.intervalScan,intervalCoverScan]
    rw [induction_hypothesis]

/-- The prototype is exactly the existing checker on projected rows. No
coefficient-cover premise or geometric conclusion replaces its computation. -/
theorem largeExponent_cheap_grid_cover_eq (layer denominator : Nat) (rows : List FiniteCoverageRow) :
    CheapGrid.cover layer denominator (largeExponentCheapGridRows rows) =
      finiteCoverageCheck layer denominator rows := by
  simp only [CheapGrid.cover,largeExponentCheapGridRows,CheapGrid.intervals,
    List.toList_toArray,List.all_map,List.any_map,List.map_map]
  rw [largeExponent_cheap_interval_scan_eq]
  rfl

theorem largeExponent_cheap_grid_accepted (layer denominator : Nat) (rows : List FiniteCoverageRow)
    (checked : CheapGrid.cover layer denominator (largeExponentCheapGridRows rows) = true) :
    finiteCoverageCheck layer denominator rows = true := by
  rw [← largeExponent_cheap_grid_cover_eq]
  exact checked

#print axioms largeExponent_cheap_grid_cover_eq
#print axioms largeExponent_cheap_grid_accepted

end LambdaCantor.RationalPowers
