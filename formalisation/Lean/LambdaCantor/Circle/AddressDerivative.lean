import LambdaCantor.First.AddressParameter
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
namespace LambdaCantor.Circle

theorem derivative_majorant_at_upper :
    (∑' index : ℕ, ((index : ℝ) + 1) * (7 / 25 : ℝ) ^ index) = 625 / 324 := by
  have norm_lt : ‖(7 / 25 : ℝ)‖ < 1 := by norm_num [Real.norm_eq_abs]
  have linear_sum := hasSum_coe_mul_geometric_of_norm_lt_one norm_lt
  have constant_sum := summable_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 7 / 25) (by norm_num : (7 / 25 : ℝ) < 1)
  calc
    _ = (∑' index : ℕ, (index : ℝ) * (7 / 25 : ℝ) ^ index) +
        ∑' index : ℕ, (7 / 25 : ℝ) ^ index := by
      rw [← linear_sum.summable.tsum_add constant_sum]
      apply tsum_congr
      intro index
      ring
    _ = 625 / 324 := by
      rw [linear_sum.tsum_eq, tsum_geometric_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 7 / 25) (by norm_num : (7 / 25 : ℝ) < 1)]
      norm_num

/-- The uniform bound 3 quoted in the circle root construction, now for the
actual parameter derivative of every infinite binary address. -/
theorem address_derivative_le_three {ratio : ℝ}
    (nonnegative : 0 ≤ ratio) (bounded : ratio ≤ (7 / 25 : ℝ)) (digits : ℕ → Bool) :
    |addressParameterDerivative ratio digits| ≤ 3 := by
  have less_one : ratio < 1 := by linarith
  have derivative_terms_nonnegative : ∀ index : ℕ,
      0 ≤ (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index := by
    intro index
    split_ifs <;> positivity
  have derivative_terms_bounded : ∀ index : ℕ,
      (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index ≤
        ((index : ℝ) + 1) * (7 / 25 : ℝ) ^ index := by
    intro index
    split_ifs
    · simp only [one_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ nonnegative bounded index) (by positivity)
    · simp only [zero_mul]
      positivity
  have majorant_summable := summable_address_derivative_majorant
    (by norm_num : (0 : ℝ) ≤ 7 / 25) (by norm_num : (7 / 25 : ℝ) < 1)
  have derivative_summable := Summable.of_nonneg_of_le derivative_terms_nonnegative derivative_terms_bounded majorant_summable
  have derivative_sum_bound := derivative_summable.tsum_le_tsum derivative_terms_bounded majorant_summable
  rw [derivative_majorant_at_upper] at derivative_sum_bound
  have derivative_sum_nonnegative : 0 ≤ ∑' index : ℕ,
      (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index :=
    tsum_nonneg derivative_terms_nonnegative
  have series_nonnegative : 0 ≤ ∑' index : ℕ,
      (if digits index then (1 : ℝ) else 0) * ratio ^ index := by
    apply tsum_nonneg
    intro index
    split_ifs <;> positivity
  have series_bound := (address_summable nonnegative less_one digits).tsum_le_tsum
    (fun index => show (if digits index then (1 : ℝ) else 0) * ratio ^ index ≤ (7 / 25 : ℝ) ^ index by
      split_ifs
      · simpa using pow_le_pow_left₀ nonnegative bounded index
      · simp [pow_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 25)])
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 7 / 25) (by norm_num : (7 / 25 : ℝ) < 1))
  rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 7 / 25) (by norm_num : (7 / 25 : ℝ) < 1)] at series_bound
  have product_nonnegative : 0 ≤ (1 - ratio) * (∑' index : ℕ,
      (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index) :=
    mul_nonneg (by linarith) derivative_sum_nonnegative
  have product_bound : (1 - ratio) * (∑' index : ℕ,
      (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index) ≤ 625 / 324 := by
    nlinarith [mul_nonneg nonnegative derivative_sum_nonnegative]
  unfold addressParameterDerivative
  apply abs_le.mpr
  constructor <;> nlinarith

end LambdaCantor.Circle
