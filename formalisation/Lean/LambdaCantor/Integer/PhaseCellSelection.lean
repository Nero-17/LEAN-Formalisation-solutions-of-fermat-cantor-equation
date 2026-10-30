import LambdaCantor.Integer.TailPhaseChecker
import Mathlib.Algebra.Order.Floor.Semiring

namespace LambdaCantor.Integer

/-- Closed half-step coefficient cells cover an entire consecutive index run,
including the two outer endpoints. -/
theorem coefficient_cell_selection (first last : ℕ) (ordered : first ≤ last)
    (positive : 0 < first) (coefficient : ℝ)
    (lower : 2*(first : ℝ)-1 ≤ 4000*coefficient)
    (upper : 4000*coefficient ≤ 2*(last : ℝ)+1) :
    ∃ cell : ℕ, first ≤ cell ∧ cell ≤ last ∧
      2*(cell : ℝ)-1 ≤ 4000*coefficient ∧ 4000*coefficient ≤ 2*(cell : ℝ)+1 := by
  have firstPositive : (1 : ℝ) ≤ first := by exact_mod_cast positive
  have nonnegative : 0 ≤ (4000*coefficient+1)/2 := by linarith
  have floorLower : first ≤ ⌊(4000*coefficient+1)/2⌋₊ := Nat.le_floor (by linarith)
  refine ⟨min last ⌊(4000*coefficient+1)/2⌋₊,le_min ordered floorLower,min_le_left _ _,?_,?_⟩
  · have minBound : ((min last ⌊(4000*coefficient+1)/2⌋₊ : ℕ) : ℝ) ≤
        (⌊(4000*coefficient+1)/2⌋₊ : ℝ) := by exact_mod_cast min_le_right last ⌊(4000*coefficient+1)/2⌋₊
    have floorBound := Nat.floor_le nonnegative
    linarith
  · by_cases truncated : last ≤ ⌊(4000*coefficient+1)/2⌋₊
    · simpa only [min_eq_left truncated] using upper
    · rw [min_eq_right (le_of_not_ge truncated)]
      have floorBound := Nat.lt_floor_add_one ((4000*coefficient+1)/2)
      linarith

end LambdaCantor.Integer
