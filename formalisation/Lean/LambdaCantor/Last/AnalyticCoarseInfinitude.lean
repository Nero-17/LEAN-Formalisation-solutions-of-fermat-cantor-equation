import LambdaCantor.Common
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

noncomputable section
namespace LambdaCantor.Last

/-- The outer shells used by the rational endpoint construction are disjoint.
The exponent step can be any positive integer, in particular the reduced
denominator of a rational exponent. -/
theorem separated_outer_shells {ratio : ℝ} (positive : 0 < ratio)
    (less_half : ratio < 1/2) {firstDepth secondDepth : ℕ}
    (depth_lt : firstDepth < secondDepth) :
    ratio ^ secondDepth < (1-ratio) * ratio ^ firstDepth := by
  have ratio_less_one : ratio < 1 := by linarith
  have power_le : ratio ^ secondDepth ≤ ratio ^ (firstDepth+1) :=
    pow_le_pow_of_le_one positive.le ratio_less_one.le depth_lt
  rw [pow_succ] at power_le
  have gap : ratio < 1-ratio := by linarith
  exact power_le.trans_lt (by nlinarith [pow_pos positive firstDepth])

/-- Actual shell witnesses imply infinitely many actual intersections.
No numeric source table and no finite approximation is used in this step. -/
theorem infinite_intersection_of_outer_shell_witnesses {exponent ratio : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2)
    {step offset : ℕ} (step_positive : 0 < step)
    (witnesses : ∀ index : ℕ, ∃ point ∈ intersection exponent ratio,
      (1-ratio)*ratio ^ (step*(index+offset)) ≤ point.1 ∧
        point.1 ≤ ratio ^ (step*(index+offset))) :
    (intersection exponent ratio).Infinite := by
  classical
  choose points membership lower_bound upper_bound using witnesses
  have first_strict : ∀ first second : ℕ, first < second → (points second).1 < (points first).1 := by
    intro first second less
    have depth_lt : step*(first+offset) < step*(second+offset) :=
      Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_right less offset) step_positive
    exact (upper_bound second).trans_lt
      ((separated_outer_shells positive less_half depth_lt).trans_le (lower_bound first))
  have injective : Function.Injective points := by
    intro first second equal
    rcases lt_trichotomy first second with less | same | greater
    · have contradiction := first_strict first second less
      rw [equal] at contradiction
      exact (lt_irrefl _ contradiction).elim
    · exact same
    · have contradiction := first_strict second first greater
      rw [equal] at contradiction
      exact (lt_irrefl _ contradiction).elim
  exact (Set.infinite_range_of_injective injective).mono (by
    rintro point ⟨index, rfl⟩
    exact membership index)

end LambdaCantor.Last
