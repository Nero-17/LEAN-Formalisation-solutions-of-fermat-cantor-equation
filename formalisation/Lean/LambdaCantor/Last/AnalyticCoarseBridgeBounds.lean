import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor.Last

/-- A rational uniform margin for the polynomial controlling the right
logarithmic bridge. The interval slightly contains the paper's parameter range. -/
theorem coarse_bridge_cubic_margin {ratio : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio ≤ 1 / 2) :
    13 / 2000 ≤ 3 * ratio - 1 - ratio ^ 3 := by
  have hnonnegative : 0 ≤ ratio := by linarith
  have hsquare : ratio ^ 2 ≤ 1 / 4 := by nlinarith
  have hcube : ratio ^ 3 ≤ ratio / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hsquare hnonnegative]
  nlinarith

/-- Every cylinder in the outer interval has the same positive algebraic
right-bridge margin, including when the quadratic coefficient changes sign. -/
theorem coarse_bridge_polynomial_margin {ratio relativeLength : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hlength : 0 ≤ relativeLength)
    (hlength_upper : relativeLength ≤ ratio / (1 - ratio)) :
    13 / 2000 ≤
      (3 * ratio - 1) + (3 * ratio - 1 - ratio ^ 2) * relativeLength := by
  have hratio : 0 < ratio := by linarith
  have hone : 0 < 1 - ratio := by linarith
  have hscaled := (le_div_iff₀ hone).mp hlength_upper
  have hcubic := coarse_bridge_cubic_margin hlower hupper.le
  by_cases hcoefficient : 0 ≤ 3 * ratio - 1 - ratio ^ 2
  · have := mul_nonneg hcoefficient hlength
    nlinarith
  · have hcoefficient_negative : 3 * ratio - 1 - ratio ^ 2 < 0 :=
      lt_of_not_ge hcoefficient
    have hproduct := mul_le_mul_of_nonpos_left hscaled hcoefficient_negative.le
    have hscaled_margin : 13 / 2000 ≤ (1 - ratio) *
        ((3 * ratio - 1) + (3 * ratio - 1 - ratio ^ 2) * relativeLength) := by
      nlinarith
    have hpositive : 0 <
        (3 * ratio - 1) + (3 * ratio - 1 - ratio ^ 2) * relativeLength := by
      nlinarith
    nlinarith

theorem coarse_bridge_product_margin {ratio relativeLength : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hlength : 0 ≤ relativeLength)
    (hlength_upper : relativeLength ≤ ratio / (1 - ratio)) :
    13 / 2000 * relativeLength ≤
      (1 + relativeLength) * (1 + ratio * relativeLength) -
        (1 + (1 - ratio) * relativeLength) ^ 2 := by
  have hmargin := mul_le_mul_of_nonneg_right
    (coarse_bridge_polynomial_margin hlower hupper hlength hlength_upper) hlength
  nlinarith

/-- Actual logarithmic right bridge is strictly longer than the central gap.
This has no thickness or intersection theorem as a hypothesis. -/
theorem coarse_log_right_bridge_gt_gap {ratio relativeLength : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hlength : 0 < relativeLength)
    (hlength_upper : relativeLength ≤ ratio / (1 - ratio)) :
    Real.log ((1 + (1 - ratio) * relativeLength) /
      (1 + ratio * relativeLength)) <
    Real.log ((1 + relativeLength) /
      (1 + (1 - ratio) * relativeLength)) := by
  have hratio : 0 < ratio := by linarith
  have hone : 0 < 1 - ratio := by linarith
  have hleft : 0 < 1 + ratio * relativeLength := by positivity
  have hmiddle : 0 < 1 + (1 - ratio) * relativeLength := by positivity
  have hmargin := coarse_bridge_product_margin hlower hupper hlength.le hlength_upper
  have hproduct : (1 + (1 - ratio) * relativeLength) ^ 2 <
      (1 + relativeLength) * (1 + ratio * relativeLength) := by nlinarith
  apply Real.strictMonoOn_log (div_pos hmiddle hleft) (div_pos (by positivity) hmiddle)
  exact (div_lt_div_iff₀ hleft hmiddle).mpr (by nlinarith)

end LambdaCantor.Last
