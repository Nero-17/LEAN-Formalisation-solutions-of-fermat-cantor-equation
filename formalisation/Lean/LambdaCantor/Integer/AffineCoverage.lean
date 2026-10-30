import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace LambdaCantor.Integer

/-- The three adjacent overlaps of the four affine child-image intervals. -/
def switchSet (r : ℝ) : Set ℝ :=
  Set.Icc (1/3) ((r+1)/6) ∪
  Set.Icc (r/3) ((r+3)/6) ∪
  Set.Icc ((r+1)/3) ((3*r+1)/6)

/-- Exact interval coverage used to construct nonempty affine Cantor fibres. -/
theorem affine_children_cover (r u : ℝ) (lower : 1 ≤ r) (upper : r ≤ 3)
    (hu : 0 ≤ u ∧ u ≤ (r+1)/2) :
    (0 ≤ 3*u ∧ 3*u ≤ (r+1)/2) ∨
    (0 ≤ 3*u-1 ∧ 3*u-1 ≤ (r+1)/2) ∨
    (0 ≤ 3*u-r ∧ 3*u-r ≤ (r+1)/2) ∨
    (0 ≤ 3*u-(r+1) ∧ 3*u-(r+1) ≤ (r+1)/2) := by
  by_cases h₀ : u ≤ (r+1)/6
  · left; constructor <;> linarith
  · by_cases h₁ : u ≤ (r+3)/6
    · right; left; constructor <;> linarith
    · by_cases h₂ : u ≤ (3*r+1)/6
      · right; right; left; constructor <;> linarith
      · right; right; right; constructor <;> linarith

/-- Every switch level lies in two adjacent child images. This statement
keeps the two different first labels explicit rather than identifying two
continuations without a separate address-separation proof. -/
theorem switch_two_children (r u : ℝ) (lower : 1 ≤ r) (upper : r ≤ 3)
    (hu : u ∈ switchSet r) :
    ((0 ≤ 3*u ∧ 3*u ≤ (r+1)/2) ∧
      (0 ≤ 3*u-1 ∧ 3*u-1 ≤ (r+1)/2)) ∨
    ((0 ≤ 3*u-1 ∧ 3*u-1 ≤ (r+1)/2) ∧
      (0 ≤ 3*u-r ∧ 3*u-r ≤ (r+1)/2)) ∨
    ((0 ≤ 3*u-r ∧ 3*u-r ≤ (r+1)/2) ∧
      (0 ≤ 3*u-(r+1) ∧ 3*u-(r+1) ≤ (r+1)/2)) := by
  rcases hu with (h | h) | h
  · left; rcases h with ⟨hlo, hhi⟩; constructor <;> constructor <;> linarith
  · right; left; rcases h with ⟨hlo, hhi⟩; constructor <;> constructor <;> linarith
  · right; right; rcases h with ⟨hlo, hhi⟩; constructor <;> constructor <;> linarith

theorem nonadjacent_child_gap (r : ℝ) :
    r/3 - (r+1)/6 = (r-1)/6 := by ring

end LambdaCantor.Integer
