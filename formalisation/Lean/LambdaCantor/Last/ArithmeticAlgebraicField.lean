import LambdaCantor.Last.AnalyticIsolatedPeriodic
import Mathlib.RingTheory.Algebraic.Integral

noncomputable section
namespace LambdaCantor.Last

theorem isAlgebraic_of_mem_parameterField {ratio coordinate : ℝ}
    (ratio_algebraic : IsAlgebraic ℚ ratio) (membership : coordinate ∈ parameterField ratio) :
    IsAlgebraic ℚ coordinate := by
  obtain ⟨expression, rfl⟩ := membership
  induction expression with
  | zero => exact isAlgebraic_zero
  | one => exact isAlgebraic_one
  | parameter => exact ratio_algebraic
  | add first second first_algebraic second_algebraic => exact first_algebraic.add second_algebraic
  | mul first second first_algebraic second_algebraic => exact first_algebraic.mul second_algebraic
  | neg expression algebraic => exact algebraic.neg
  | inv expression algebraic => exact algebraic.inv

theorem address_tail_algebraic {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1)
    (ratio_algebraic : IsAlgebraic ℚ ratio) (digits : ℕ → Bool)
    (coordinate_algebraic : IsAlgebraic ℚ (address ratio digits)) (depth : ℕ) :
    IsAlgebraic ℚ (address ratio (fun index => digits (index+depth))) := by
  have prefix_algebraic := isAlgebraic_of_mem_parameterField ratio_algebraic
    (prefixValue_mem_parameterField ratio digits depth)
  have split := address_prefix_tail positive.le less_one digits depth
  have tail_eq : address ratio (fun index => digits (index+depth)) =
      (address ratio digits-prefixValue ratio digits depth)/ratio^depth := by
    apply (eq_div_iff (pow_pos positive depth).ne').mpr
    nlinarith
  rw [tail_eq, div_eq_mul_inv]
  exact (coordinate_algebraic.sub prefix_algebraic).mul ((ratio_algebraic.pow depth).inv)

theorem address_mem_parameterField_of_tail {ratio : ℝ}
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1) (digits : ℕ → Bool) (depth : ℕ)
    (tail_mem : address ratio (fun index => digits (index+depth)) ∈ parameterField ratio) :
    address ratio digits ∈ parameterField ratio := by
  rw [address_prefix_tail nonnegative less_one digits depth]
  exact (parameterField ratio).add_mem (prefixValue_mem_parameterField ratio digits depth)
    ((parameterField ratio).mul_mem
      ((parameterField ratio).pow_mem (ratio_mem_parameterField ratio) depth) tail_mem)

end LambdaCantor.Last
