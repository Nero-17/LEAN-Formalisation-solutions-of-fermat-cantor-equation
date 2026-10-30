import LambdaCantor.Last.AnalyticCoarseBridgeBounds

noncomputable section
namespace LambdaCantor.Last

/-- Quantitative logarithmic surplus of the right bridge over the gap.
The surplus is uniform down to cylinders of arbitrarily small relative length. -/
theorem coarse_log_bridge_surplus {ratio relativeLength : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hlength : 0 ≤ relativeLength)
    (hlength_upper : relativeLength ≤ ratio / (1 - ratio)) :
    13 / 8000 * relativeLength ≤ Real.log
      (((1 + relativeLength) * (1 + ratio * relativeLength)) /
        (1 + (1 - ratio) * relativeLength) ^ 2) := by
  have hratio : 0 < ratio := by linarith
  have hone : 0 < 1 - ratio := by linarith
  have hscaled := (le_div_iff₀ hone).mp hlength_upper
  have hlength_one : relativeLength ≤ 1 := by nlinarith
  have hleft : 0 < 1 + ratio * relativeLength := by positivity
  have hmiddle : 0 < 1 + (1 - ratio) * relativeLength := by positivity
  have hproduct : 0 < (1 + relativeLength) * (1 + ratio * relativeLength) :=
    mul_pos (by positivity) hleft
  have hproduct_upper : (1 + relativeLength) * (1 + ratio * relativeLength) ≤ 4 := by
    have hsecond : 1 + ratio * relativeLength ≤ 2 := by nlinarith
    calc
      _ ≤ 2 * 2 := mul_le_mul (by linarith : 1 + relativeLength ≤ 2)
        hsecond hleft.le (by norm_num)
      _ = 4 := by norm_num
  have hmargin := coarse_bridge_product_margin hlower hupper hlength hlength_upper
  have hscaled_upper := mul_le_mul_of_nonneg_left hproduct_upper
    (show 0 ≤ 13 / 8000 * relativeLength by positivity)
  have hlower_fraction : 13 / 8000 * relativeLength ≤
      ((1 + relativeLength) * (1 + ratio * relativeLength) -
        (1 + (1 - ratio) * relativeLength) ^ 2) /
      ((1 + relativeLength) * (1 + ratio * relativeLength)) := by
    apply (le_div_iff₀ hproduct).mpr
    nlinarith
  have hlog := Real.one_sub_inv_le_log_of_pos
    (div_pos hproduct (sq_pos_of_pos hmiddle))
  have hfraction :
      ((1 + relativeLength) * (1 + ratio * relativeLength) -
        (1 + (1 - ratio) * relativeLength) ^ 2) /
        ((1 + relativeLength) * (1 + ratio * relativeLength)) =
      1 - (((1 + relativeLength) * (1 + ratio * relativeLength)) /
        (1 + (1 - ratio) * relativeLength) ^ 2)⁻¹ := by
    rw [inv_div]
    field_simp [hproduct.ne']
    <;> ring
  rw [← hfraction] at hlog
  exact hlower_fraction.trans hlog

theorem coarse_log_gap_le_relativeLength {ratio relativeLength : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio ≤ 1 / 2) (hlength : 0 ≤ relativeLength) :
    Real.log ((1 + (1 - ratio) * relativeLength) /
      (1 + ratio * relativeLength)) ≤ relativeLength := by
  have hleft : 0 < 1 + ratio * relativeLength := by positivity
  have hmiddle : 0 < 1 + (1 - ratio) * relativeLength := by
    have : 0 ≤ 1 - ratio := by linarith
    positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hmiddle hleft)
  have hbound : (1 + (1 - ratio) * relativeLength) /
      (1 + ratio * relativeLength) - 1 ≤ relativeLength := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hleft).mpr
    nlinarith [mul_nonneg hratio hlength, mul_nonneg hratio (sq_nonneg relativeLength)]
  exact hlog.trans hbound

/-- Both logarithmic intervals are the actual adjacent bridge and central
gap of a cylinder; the right bridge has a fixed ratio strictly above one. -/
theorem coarse_log_right_bridge_uniform {ratio relativeLength : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hlength : 0 ≤ relativeLength)
    (hlength_upper : relativeLength ≤ ratio / (1 - ratio)) :
    (1 + 13 / 8000) * Real.log
      ((1 + (1 - ratio) * relativeLength) / (1 + ratio * relativeLength)) ≤
    Real.log ((1 + relativeLength) / (1 + (1 - ratio) * relativeLength)) := by
  have hratio : 0 < ratio := by linarith
  have hone : 0 < 1 - ratio := by linarith
  have hleft : 0 < 1 + ratio * relativeLength := by positivity
  have hmiddle : 0 < 1 + (1 - ratio) * relativeLength := by positivity
  have htop : 0 < 1 + relativeLength := by positivity
  have hsurplus := coarse_log_bridge_surplus hlower hupper hlength hlength_upper
  have hgap := coarse_log_gap_le_relativeLength hratio.le hupper.le hlength
  rw [Real.log_div (mul_pos htop hleft).ne' (sq_pos_of_pos hmiddle).ne',
    Real.log_mul htop.ne' hleft.ne', Real.log_pow] at hsurplus
  rw [Real.log_div hmiddle.ne' hleft.ne'] at hgap
  rw [Real.log_div hmiddle.ne' hleft.ne', Real.log_div htop.ne' hmiddle.ne']
  nlinarith

end LambdaCantor.Last
