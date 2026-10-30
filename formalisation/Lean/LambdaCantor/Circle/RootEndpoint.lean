import LambdaCantor.Circle.RootResidual
import LambdaCantor.Circle.Onset
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp

noncomputable section
namespace LambdaCantor.Circle

/-- Uniform sign at the fixed right endpoint, for every pair of bounded tails. -/
theorem right_endpoint_residual_negative (scale firstTail secondTail : ℝ)
    (scale_nonnegative : 0 ≤ scale) (scale_upper : scale ≤ (7 / 25 : ℝ) ^ 2)
    (first_nonnegative : 0 ≤ firstTail) (first_upper : firstTail ≤ 1)
    (second_nonnegative : 0 ≤ secondTail) (second_upper : secondTail ≤ 1) :
    -(4 * (7 / 25 : ℝ) - 1 - (7 / 25 : ℝ) ^ 2) +
      2 * (7 / 25 : ℝ) * scale ^ 2 * ((1 - (7 / 25 : ℝ)) * firstTail + secondTail) +
      (7 / 25 : ℝ) ^ 2 * scale ^ 4 * firstTail ^ 2 +
      (7 / 25 : ℝ) ^ 2 * scale ^ 2 * (1 - scale ^ 2 * secondTail) ^ 2 < 0 := by
  have square_bound : scale ^ 2 ≤ (7 / 25 : ℝ) ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr scale_upper) (add_nonneg scale_nonnegative (by norm_num : (0 : ℝ) ≤ (7 / 25) ^ 2))]
  have fourth_bound : scale ^ 4 ≤ (7 / 25 : ℝ) ^ 8 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr square_bound) (add_nonneg (sq_nonneg scale) (by norm_num : (0 : ℝ) ≤ (7 / 25) ^ 4))]
  have first_square : firstTail ^ 2 ≤ 1 := by nlinarith
  have inner_bounds : 0 ≤ 1 - scale ^ 2 * secondTail ∧ 1 - scale ^ 2 * secondTail ≤ 1 := by
    have product_upper : scale ^ 2 * secondTail ≤ scale ^ 2 := by nlinarith [sq_nonneg scale]
    constructor <;> nlinarith [mul_nonneg (sq_nonneg scale) second_nonnegative]
  have inner_square : (1 - scale ^ 2 * secondTail) ^ 2 ≤ 1 := by nlinarith [inner_bounds.1, inner_bounds.2]
  have first_term : 2 * (7 / 25 : ℝ) * scale ^ 2 * ((1 - (7 / 25 : ℝ)) * firstTail + secondTail) ≤
      2 * (7 / 25 : ℝ) ^ 5 * (2 - 7 / 25) := by
    calc
      _ ≤ 2 * (7 / 25 : ℝ) * (7 / 25 : ℝ) ^ 4 * ((1 - (7 / 25 : ℝ)) * 1 + 1) := by gcongr
      _ = _ := by ring
  have second_term : (7 / 25 : ℝ) ^ 2 * scale ^ 4 * firstTail ^ 2 ≤ (7 / 25 : ℝ) ^ 10 := by
    calc
      _ ≤ (7 / 25 : ℝ) ^ 2 * (7 / 25 : ℝ) ^ 8 * 1 := by gcongr
      _ = _ := by ring
  have third_term : (7 / 25 : ℝ) ^ 2 * scale ^ 2 * (1 - scale ^ 2 * secondTail) ^ 2 ≤ (7 / 25 : ℝ) ^ 6 := by
    calc
      _ ≤ (7 / 25 : ℝ) ^ 2 * (7 / 25 : ℝ) ^ 4 * 1 := by gcongr
      _ = _ := by ring
  norm_num at first_term second_term third_term ⊢
  linarith

end LambdaCantor.Circle

