import LambdaCantor.Last.AnalyticCoarseGapBounds

noncomputable section
namespace LambdaCantor.Last

def coarseLogHullLength (ratio : ℝ) : ℝ := -Real.log (1 - ratio)
def coarseLogPeriodLength (ratio : ℝ) : ℝ := -Real.log ratio
def coarseLogRootGapLength (ratio : ℝ) : ℝ :=
  Real.log (1 - ratio ^ 2) - Real.log (1 - ratio + ratio ^ 2)
def coarseLogRootRightBridge (ratio : ℝ) : ℝ :=
  Real.log (1 - ratio + ratio ^ 2) - Real.log (1 - ratio)

theorem coarse_moderate_root_data {ratio : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2) :
    0 < coarseLogRootGapLength ratio ∧
      0 < coarseLogRootRightBridge ratio ∧
      0 < coarseLogPeriodLength ratio - coarseLogHullLength ratio ∧
      coarseLogRootGapLength ratio * (coarseLogPeriodLength ratio - coarseLogHullLength ratio) <
        coarseLogHullLength ratio * coarseLogRootRightBridge ratio ∧
      ∀ exponent : ℝ, 3 ≤ exponent → exponent ≤ 6 →
        coarseLogPeriodLength ratio < exponent * coarseLogHullLength ratio ∧
        exponent * coarseLogRootGapLength ratio < coarseLogPeriodLength ratio + coarseLogHullLength ratio ∧
        exponent * (2 / 27) < coarseLogHullLength ratio := by
  have hratio : 0 < ratio := by linarith
  have hone : 0 < 1 - ratio := by linarith
  have hnum : 0 < 1 - ratio ^ 2 := by nlinarith
  have hden : 0 < 1 - ratio + ratio ^ 2 := by positivity
  have hhull := (coarse_log_hull_period_bounds hlower hupper).1
  have hperiod := (coarse_log_hull_period_bounds hlower hupper).2.1
  have hroot := coarse_root_log_gap_lt_rational hlower hupper
  rw [Real.log_div hnum.ne' hden.ne'] at hroot
  have hbridge := coarse_log_right_root_bridge_gt_rational hlower hupper
  rw [Real.log_div hden.ne' hone.ne'] at hbridge
  have hroot_positive : 0 < coarseLogRootGapLength ratio := by
    have horder : 1 - ratio + ratio ^ 2 < 1 - ratio ^ 2 := by
      nlinarith [mul_pos hratio (show 0 < 1 - 2 * ratio by linarith)]
    exact sub_pos.mpr (Real.strictMonoOn_log hden hnum horder)
  have hbridge_positive : 0 < coarseLogRootRightBridge ratio := by
    dsimp [coarseLogRootRightBridge]
    linarith
  have hdifference : 0 < coarseLogPeriodLength ratio - coarseLogHullLength ratio := by
    have horder := Real.strictMonoOn_log hratio hone (show ratio < 1 - ratio by linarith)
    dsimp [coarseLogPeriodLength, coarseLogHullLength]
    linarith
  have hperiod_lower : (1 / 2 : ℝ) < coarseLogPeriodLength ratio := by
    have hlog := Real.log_le_sub_one_of_pos hratio
    dsimp [coarseLogPeriodLength]
    linarith
  have hdifference_upper : coarseLogPeriodLength ratio - coarseLogHullLength ratio < 54961 / 100000 := by
    dsimp [coarseLogPeriodLength, coarseLogHullLength]
    linarith
  have hhull_positive : 0 < coarseLogHullLength ratio := by
    dsimp [coarseLogHullLength]
    linarith
  have hroot_upper : coarseLogRootGapLength ratio < 12021 / 100000 := hroot
  have hbridge_lower : 16 / 93 < coarseLogRootRightBridge ratio := hbridge
  have hproduct_lower :=
    (mul_lt_mul_of_pos_right hhull (by norm_num : (0 : ℝ) < 16 / 93)).trans
      (mul_lt_mul_of_pos_left hbridge_lower hhull_positive)
  have hproduct_upper :=
    (mul_lt_mul_of_pos_right hroot_upper hdifference).trans
      (mul_lt_mul_of_pos_left hdifference_upper (by norm_num : (0 : ℝ) < 12021 / 100000))
  refine ⟨hroot_positive, hbridge_positive, hdifference, ?_, ?_⟩
  · dsimp [coarseLogHullLength] at hproduct_lower hproduct_upper ⊢
    nlinarith
  · intro exponent hexponent_lower hexponent_upper
    have hlarge := mul_le_mul_of_nonneg_right hexponent_lower hhull_positive.le
    have hsmall := mul_le_mul_of_nonneg_right hexponent_upper hroot_positive.le
    dsimp [coarseLogHullLength] at hlarge ⊢
    dsimp [coarseLogPeriodLength] at hperiod_lower ⊢
    dsimp [coarseLogRootGapLength] at hsmall hroot_upper ⊢
    constructor
    · nlinarith
    constructor <;> nlinarith

end LambdaCantor.Last
