import LambdaCantor.Last.AnalyticCoarseNumericLogs
import LambdaCantor.Last.AnalyticCoarseGapCertificates
import Mathlib.Tactic.Positivity

noncomputable section
namespace LambdaCantor.Last

theorem coarse_root_log_base_upper :
    Real.log (216511 / 191989 : ℝ) < 12021 / 100000 := by
  have hseries := Real.log_div_le_sum_range_add
    (show (0 : ℝ) ≤ 12261 / 204250 by norm_num)
    (show (12261 / 204250 : ℝ) < 1 by norm_num) 3
  norm_num [Finset.sum_range_succ] at hseries
  linarith

theorem coarse_left_child_log_base_upper :
    Real.log (89866013 / 85378487 : ℝ) < 5123 / 100000 := by
  have hseries := Real.log_div_le_sum_range_add
    (show (0 : ℝ) ≤ 2243763 / 87622250 by norm_num)
    (show (2243763 / 87622250 : ℝ) < 1 by norm_num) 3
  norm_num [Finset.sum_range_succ] at hseries
  linarith

theorem coarse_right_child_log_base_upper :
    Real.log (118871513 / 114383987 : ℝ) < 3849 / 100000 := by
  have hseries := Real.log_div_le_sum_range_add
    (show (0 : ℝ) ≤ 2243763 / 116627750 by norm_num)
    (show (2243763 / 116627750 : ℝ) < 1 by norm_num) 3
  norm_num [Finset.sum_range_succ] at hseries
  linarith

theorem coarse_root_log_gap_lt_rational {ratio : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2) :
    Real.log ((1 - ratio ^ 2) / (1 - ratio + ratio ^ 2)) < 12021 / 100000 := by
  have hratio : 0 < ratio := by linarith
  have hone : 0 < 1 - ratio := by linarith
  have hden : 0 < 1 - ratio + ratio ^ 2 := by positivity
  have hnum : 0 < 1 - ratio ^ 2 := by nlinarith
  have hquotient : (1 - ratio ^ 2) / (1 - ratio + ratio ^ 2) ≤ 216511 / 191989 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [coarse_root_ratio_certificate hlower hupper.le]
  exact (Real.strictMonoOn_log.monotoneOn (div_pos hnum hden) (by norm_num) hquotient).trans_lt
    coarse_root_log_base_upper

theorem coarse_log_right_root_bridge_gt_rational {ratio : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2) :
    16 / 93 < Real.log ((1 - ratio + ratio ^ 2) / (1 - ratio)) := by
  have hone : 0 < 1 - ratio := by linarith
  have hden : 0 < 1 - ratio + ratio ^ 2 := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hden hone)
  have hidentity : ratio ^ 2 / (1 - ratio + ratio ^ 2) =
      1 - ((1 - ratio + ratio ^ 2) / (1 - ratio))⁻¹ := by
    rw [inv_div]
    field_simp [hden.ne']
    <;> ring
  have hsquare : (183 / 500 : ℝ) ^ 2 ≤ ratio ^ 2 := by
    nlinarith [sq_nonneg (ratio - 183 / 500)]
  have hbound : (16 / 93 : ℝ) < ratio ^ 2 / (1 - ratio + ratio ^ 2) := by
    apply (lt_div_iff₀ hden).mpr
    nlinarith
  rw [← hidentity] at hlog
  exact hbound.trans_le hlog

theorem coarse_three_log_gap_bounds {ratio : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2) :
    Real.log ((1 - ratio ^ 2) / (1 - ratio + ratio ^ 2)) <
        33 / 125 * (-Real.log (1 - ratio)) ∧
      Real.log (((1 - ratio) * (1 + ratio ^ 2)) / (1 - ratio + ratio ^ 3)) <
        113 / 1000 * (-Real.log (1 - ratio)) ∧
      Real.log ((1 - ratio ^ 3) / (1 - ratio ^ 2 + ratio ^ 3)) <
        17 / 200 * (-Real.log (1 - ratio)) := by
  have hratio : 0 < ratio := by linarith
  have hone : 0 < 1 - ratio := by linarith
  have hsquare : ratio ^ 2 < 1 := by nlinarith
  have hcube : ratio ^ 3 < 1 := by
    have := mul_lt_mul_of_pos_left hsquare hratio
    nlinarith
  have hden_root : 0 < 1 - ratio + ratio ^ 2 := by positivity
  have hden_left : 0 < 1 - ratio + ratio ^ 3 := by positivity
  have hden_right : 0 < 1 - ratio ^ 2 + ratio ^ 3 := by positivity
  have hhull := (coarse_log_hull_period_bounds hlower hupper).1
  have hroot_ratio : (1 - ratio ^ 2) / (1 - ratio + ratio ^ 2) ≤
      216511 / 191989 := by
    apply (div_le_iff₀ hden_root).mpr
    nlinarith [coarse_root_ratio_certificate hlower hupper.le]
  have hleft_ratio : ((1 - ratio) * (1 + ratio ^ 2)) / (1 - ratio + ratio ^ 3) ≤
      89866013 / 85378487 := by
    apply (div_le_iff₀ hden_left).mpr
    nlinarith [coarse_left_child_ratio_certificate hlower hupper.le]
  have hright_ratio : (1 - ratio ^ 3) / (1 - ratio ^ 2 + ratio ^ 3) ≤
      118871513 / 114383987 := by
    apply (div_le_iff₀ hden_right).mpr
    nlinarith [coarse_right_child_ratio_certificate hlower hupper.le]
  have hroot_log := Real.strictMonoOn_log.monotoneOn
    (div_pos (by linarith : 0 < 1 - ratio ^ 2) hden_root) (by norm_num) hroot_ratio
  have hleft_log := Real.strictMonoOn_log.monotoneOn
    (div_pos (mul_pos hone (by positivity)) hden_left) (by norm_num) hleft_ratio
  have hright_log := Real.strictMonoOn_log.monotoneOn
    (div_pos (by linarith : 0 < 1 - ratio ^ 3) hden_right) (by norm_num) hright_ratio
  constructor
  · linarith [coarse_root_log_base_upper]
  constructor
  · linarith [coarse_left_child_log_base_upper]
  · linarith [coarse_right_child_log_base_upper]

end LambdaCantor.Last
