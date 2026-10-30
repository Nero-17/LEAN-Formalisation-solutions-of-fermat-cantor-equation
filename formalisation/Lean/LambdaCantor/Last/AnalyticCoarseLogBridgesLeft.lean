import LambdaCantor.Last.AnalyticCoarseBridgeBounds

noncomputable section
namespace LambdaCantor.Last

theorem coarse_log_left_bridge_uniform {ratio relativeLength : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hlength : 0 ≤ relativeLength) :
    (1 + 13 / 8000) * Real.log
      ((1 + (1 - ratio) * relativeLength) / (1 + ratio * relativeLength)) ≤
    Real.log (1 + ratio * relativeLength) := by
  have hratio : 0 < ratio := by linarith
  have hleft : 0 < 1 + ratio * relativeLength := by positivity
  have hmiddle : 0 < 1 + (1 - ratio) * relativeLength := by
    have : 0 < 1 - ratio := by linarith
    positivity
  have hbridge := Real.one_sub_inv_le_log_of_pos hleft
  have hbridge_fraction : ratio * relativeLength / (1 + ratio * relativeLength) ≤
      Real.log (1 + ratio * relativeLength) := by
    convert hbridge using 1
    field_simp [hleft.ne']
    <;> ring
  have hgap := Real.log_le_sub_one_of_pos (div_pos hmiddle hleft)
  have hgap_fraction : Real.log
      ((1 + (1 - ratio) * relativeLength) / (1 + ratio * relativeLength)) ≤
      (1 - 2 * ratio) * relativeLength / (1 + ratio * relativeLength) := by
    convert hgap using 1
    field_simp [hleft.ne']
    <;> ring
  calc
    _ ≤ (1 + 13 / 8000) *
        ((1 - 2 * ratio) * relativeLength / (1 + ratio * relativeLength)) :=
      mul_le_mul_of_nonneg_left hgap_fraction (by norm_num)
    _ ≤ ratio * relativeLength / (1 + ratio * relativeLength) := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hleft.le
      have hcoefficient : (1 + 13 / 8000) * (1 - 2 * ratio) ≤ ratio := by linarith
      nlinarith [mul_le_mul_of_nonneg_right hcoefficient hlength]
    _ ≤ _ := hbridge_fraction

/-- Logarithmic lengths on the outer hull are bounded by the extremal
derivatives of log. These estimates prove the ordering between generations. -/
theorem coarse_log_interval_bounds {ratio left right : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio < 1)
    (hlower : 1 - ratio ≤ left) (horder : left ≤ right) (hupper : right ≤ 1) :
    right - left ≤ Real.log (right / left) ∧
      Real.log (right / left) ≤ (right - left) / (1 - ratio) := by
  have hleft : 0 < left := by linarith
  have hright : 0 < right := hleft.trans_le horder
  have hone : 0 < 1 - ratio := by linarith
  have hlog_lower := Real.one_sub_inv_le_log_of_pos (div_pos hright hleft)
  have hlog_upper := Real.log_le_sub_one_of_pos (div_pos hright hleft)
  have hfirst : right - left ≤ 1 - (right / left)⁻¹ := by
    have hidentity : 1 - (right / left)⁻¹ = (right - left) / right := by
      rw [inv_div]
      field_simp [hright.ne']
      <;> ring
    rw [hidentity]
    exact (le_div_iff₀ hright).mpr
      (mul_le_of_le_one_right (sub_nonneg.mpr horder) hupper)
  have hsecond : right / left - 1 ≤ (right - left) / (1 - ratio) := by
    have hidentity : right / left - 1 = (right - left) / left := by
      field_simp [hleft.ne']
      <;> ring
    rw [hidentity]
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr horder) hone hlower
  exact ⟨hfirst.trans hlog_lower, hlog_upper.trans hsecond⟩

end LambdaCantor.Last
