import LambdaCantor.AE.MathlibBumpInnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
open Set Metric
open scoped ContDiff

namespace LambdaCantor.AE

/-- A fixed smooth profile, one on [-1/4,1/4] and supported on [-1/2,1/2]. -/
def nearBandCutoffProfile : ContDiffBump (0 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The concrete smooth cutoff in the manuscript's small-value band. -/
def nearBandCutoff (threshold value : ℝ) : ℝ := nearBandCutoffProfile (value / threshold)

theorem contDiff_nearBandCutoff (threshold : ℝ) : ContDiff ℝ ∞ (nearBandCutoff threshold) := by
  exact nearBandCutoffProfile.contDiff.comp (contDiff_id.div_const threshold)

theorem nearBandCutoff_nonneg (threshold value : ℝ) : 0 ≤ nearBandCutoff threshold value :=
  nearBandCutoffProfile.nonneg

theorem nearBandCutoff_le_one (threshold value : ℝ) : nearBandCutoff threshold value ≤ 1 :=
  nearBandCutoffProfile.le_one

theorem nearBandCutoff_eq_one {threshold value : ℝ} (hthreshold : 0 < threshold)
    (hvalue : |value| ≤ threshold / 4) : nearBandCutoff threshold value = 1 := by
  apply nearBandCutoffProfile.one_of_mem_closedBall
  have hdivide : |value| / threshold ≤ (1 / 4 : ℝ) :=
    (div_le_iff₀ hthreshold).mpr (by linarith)
  simpa only [mem_closedBall, Real.dist_eq, sub_zero, abs_div,
    abs_of_pos hthreshold, nearBandCutoffProfile] using hdivide

theorem tsupport_nearBandCutoff_subset {threshold : ℝ} (hthreshold : 0 < threshold) :
    tsupport (nearBandCutoff threshold) ⊆ Ioo (-threshold) threshold := by
  intro value hvalue
  have hpreimage := tsupport_comp_subset_preimage (nearBandCutoffProfile : ℝ → ℝ)
    (continuous_id.div_const threshold) hvalue
  change value / threshold ∈ tsupport (nearBandCutoffProfile : ℝ → ℝ) at hpreimage
  rw [nearBandCutoffProfile.tsupport_eq] at hpreimage
  have hdivide : |value| / threshold ≤ (1 / 2 : ℝ) := by
    simpa only [mem_closedBall, Real.dist_eq, sub_zero, abs_div,
      abs_of_pos hthreshold, nearBandCutoffProfile] using hpreimage
  have habsolute : |value| < threshold := by
    have hmul := (div_le_iff₀ hthreshold).mp hdivide
    linarith
  exact abs_lt.mp habsolute

/-- A single constant controls all rescaled cutoff derivatives. Its
existence is proved from the compactly supported smooth fixed profile. -/
theorem exists_nearBandCutoff_derivative_bound :
    ∃ constant : ℝ, 0 < constant ∧ ∀ threshold : ℝ, 0 < threshold → ∀ value : ℝ,
      |deriv (nearBandCutoff threshold) value| ≤ constant / threshold := by
  have hcontinuous : Continuous (deriv (nearBandCutoffProfile : ℝ → ℝ)) :=
    (nearBandCutoffProfile.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨constant, hbound⟩ := nearBandCutoffProfile.hasCompactSupport.deriv.exists_bound_of_continuous
    hcontinuous
  refine ⟨max constant 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro threshold hthreshold value
  have hprofile : Differentiable ℝ (nearBandCutoffProfile : ℝ → ℝ) :=
    (nearBandCutoffProfile.contDiff (n := 1)).differentiable_one
  have hderivative := (hprofile (value / threshold)).hasDerivAt.comp value
    ((hasDerivAt_id value).div_const threshold)
  change HasDerivAt (nearBandCutoff threshold)
    (deriv (nearBandCutoffProfile : ℝ → ℝ) (value / threshold) * (1 / threshold)) value at hderivative
  rw [hderivative.deriv, abs_mul, abs_div, abs_one, abs_of_pos hthreshold]
  calc
    _ ≤ max constant 1 * (1 / threshold) :=
      mul_le_mul_of_nonneg_right
        ((show |deriv (nearBandCutoffProfile : ℝ → ℝ) (value / threshold)| ≤ constant by
          simpa only [Real.norm_eq_abs] using hbound (value / threshold)).trans (le_max_left _ _))
        (by positivity)
    _ = _ := by rw [mul_one_div]

/-- The complementary cutoff only sees residual values at least one quarter
of the chosen band scale. This discharges the off-band support condition. -/
theorem nearBandCutoff_complement_nonzero_imp {threshold value : ℝ} (hthreshold : 0 < threshold)
    (hnonzero : 1 - nearBandCutoff threshold value ≠ 0) : threshold / 4 < |value| := by
  by_contra hnot
  have hone := nearBandCutoff_eq_one hthreshold (le_of_not_gt hnot)
  exact hnonzero (by rw [hone, sub_self])

end LambdaCantor.AE
