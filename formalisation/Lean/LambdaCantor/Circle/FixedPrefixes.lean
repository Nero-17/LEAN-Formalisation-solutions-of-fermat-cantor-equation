import LambdaCantor.First.RootsIncidence
import Mathlib.Algebra.Ring.GeomSum

noncomputable section
namespace LambdaCantor.Circle
open LambdaCantor.First.Roots

def circleHorizontalPrefix (depth : ℕ) (index : ℕ) : Bool := decide (index = depth)
def circleVerticalPrefix (depth : ℕ) (index : ℕ) : Bool := decide (index < 2 * depth + 1)

theorem circle_horizontal_prefix_value (ratio : ℝ) (depth : ℕ) :
    prefixValue ratio (circleHorizontalPrefix depth) (3 * depth + 1) = (1 - ratio) * ratio ^ depth := by
  simp [prefixValue, circleHorizontalPrefix, show depth < 3 * depth + 1 by omega]

theorem prefixValue_initial_ones (ratio : ℝ) (cut length : ℕ) (ordered : cut ≤ length) :
    prefixValue ratio (fun index => decide (index < cut)) length = 1 - ratio ^ cut := by
  have truncated :
      (∑ index ∈ Finset.range length, (if decide (index < cut) then (1 : ℝ) else 0) * ratio ^ index) =
        ∑ index ∈ Finset.range cut, ratio ^ index := by
    calc
      _ = ∑ index ∈ Finset.range cut, (if decide (index < cut) then (1 : ℝ) else 0) * ratio ^ index := by
        symm
        apply Finset.sum_subset (Finset.range_mono ordered)
        intro index in_length not_in_cut
        simp only [Finset.mem_range] at not_in_cut
        simp [not_in_cut]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro index member
        simp [Finset.mem_range.mp member]
  unfold prefixValue
  rw [truncated, mul_comm]
  exact geom_sum_mul_neg ratio cut

theorem circle_vertical_prefix_value (ratio : ℝ) (depth : ℕ) :
    prefixValue ratio (circleVerticalPrefix depth) (4 * depth + 1) = 1 - ratio ^ (2 * depth + 1) :=
  prefixValue_initial_ones ratio (2 * depth + 1) (4 * depth + 1) (by omega)

/-- The circle construction uses fixed prefixes of lengths 3k+1 and 4k+1,
with unrestricted complete tails, exactly as required by the root-fibre lemma. -/
theorem circle_cylinder_coordinates {ratio : ℝ} (depth : ℕ)
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1) (firstDigits secondDigits : ℕ → Bool) :
    address ratio (cylinderDigits (circleHorizontalPrefix depth) (3 * depth + 1) firstDigits) =
      (1 - ratio) * ratio ^ depth + ratio * (ratio ^ depth) ^ 3 * address ratio firstDigits ∧
    address ratio (cylinderDigits (circleVerticalPrefix depth) (4 * depth + 1) secondDigits) =
      1 - ratio * (ratio ^ depth) ^ 2 + ratio * (ratio ^ depth) ^ 4 * address ratio secondDigits := by
  rw [cylinder_address nonnegative less_one, cylinder_address nonnegative less_one,
    circle_horizontal_prefix_value, circle_vertical_prefix_value]
  have twice : ratio ^ (2 * depth) = (ratio ^ depth) ^ 2 := by rw [Nat.mul_comm, pow_mul]
  have thrice : ratio ^ (3 * depth) = (ratio ^ depth) ^ 3 := by rw [Nat.mul_comm, pow_mul]
  have four : ratio ^ (4 * depth) = (ratio ^ depth) ^ 4 := by rw [Nat.mul_comm, pow_mul]
  simp only [pow_succ, twice, thrice, four]
  constructor <;> ring

end LambdaCantor.Circle
