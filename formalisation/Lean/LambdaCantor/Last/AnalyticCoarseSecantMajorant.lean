import LambdaCantor.Last.AnalyticCoarseSecantComparison
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace LambdaCantor.Last

/-- The elementary lower logarithm bound gives the paper's rational secant
majorant directly, without an exponential-series estimate. -/
theorem coarse_secant_error_majorant {exponent period scale relativeWidth : ℝ}
    (hexponent : 20 ≤ exponent) (hperiod : period ≤ 503 / 500)
    (hscale_lower : 1 ≤ scale) (hscale_upper : scale ≤ 11 / 4)
    (hwidth : 0 ≤ relativeWidth)
    (hphase : scale * period = exponent * Real.log (1 + relativeWidth)) :
    exponent * relativeWidth ^ 2 / 8 ≤ coarseSecantError scale := by
  have hexponent_positive : 0 < exponent := by linarith
  have hscale_positive : 0 < scale := by linarith
  have hbase : 0 < 1 + relativeWidth := by linarith
  have hden_positive : 0 < 1 - scale * (503 / 500) / 20 := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hbase
  have hlog_fraction : relativeWidth / (1 + relativeWidth) ≤
      Real.log (1 + relativeWidth) := by
    convert hlog using 1
    field_simp [hbase.ne']
    <;> ring
  have hscaled_log := mul_le_mul_of_nonneg_left hlog_fraction hexponent_positive.le
  rw [← hphase] at hscaled_log
  have hfraction : exponent * relativeWidth / (1 + relativeWidth) ≤ scale * period := by
    calc
      exponent * relativeWidth / (1 + relativeWidth) =
          exponent * (relativeWidth / (1 + relativeWidth)) := mul_div_assoc _ _ _
      _ ≤ scale * period := hscaled_log
  have hproduct := (div_le_iff₀ hbase).mp hfraction
  have hperiod_product := mul_le_mul_of_nonneg_left hperiod hscale_positive.le
  have hperiod_scaled := mul_le_mul_of_nonneg_right hperiod_product hbase.le
  have hupper : exponent * relativeWidth ≤ scale * (503 / 500) * (1 + relativeWidth) :=
    hproduct.trans hperiod_scaled
  have hexponent_scaled := mul_le_mul_of_nonneg_right hexponent
    (show 0 ≤ scale * (503 / 500) * relativeWidth by positivity)
  have hden_product : exponent * (1 - scale * (503 / 500) / 20) * relativeWidth ≤
      scale * (503 / 500) := by
    nlinarith
  have hden_product_nonnegative :
      0 ≤ exponent * (1 - scale * (503 / 500) / 20) * relativeWidth := by positivity
  have hsquare : exponent ^ 2 * (1 - scale * (503 / 500) / 20) ^ 2 * relativeWidth ^ 2 ≤
      scale ^ 2 * (503 / 500) ^ 2 := by
    have hnonnegative := mul_nonneg (sub_nonneg.mpr hden_product)
      (show 0 ≤ scale * (503 / 500) +
        exponent * (1 - scale * (503 / 500) / 20) * relativeWidth by positivity)
    nlinarith
  have hexponent_square : 20 * exponent ≤ exponent ^ 2 := by nlinarith
  have hcomparison := mul_le_mul_of_nonneg_right hexponent_square
    (mul_nonneg (sq_nonneg (1 - scale * (503 / 500) / 20)) (sq_nonneg relativeWidth))
  rw [coarseSecantError]
  apply (le_div_iff₀ (coarse_secant_denominator_positive hscale_upper)).mpr
  nlinarith

end LambdaCantor.Last
