import LambdaCantor.AE.ScaledCutoff
import LambdaCantor.AE.MathlibFourierConvolutionCore
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff

namespace LambdaCantor.AE

def transportMollifierMass : ℝ := ∫ value : ℝ, nearBandCutoffProfile value

theorem transportMollifierMass_pos : 0 < transportMollifierMass := by
  apply nearBandCutoffProfile.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    nearBandCutoffProfile.hasCompactSupport (fun _ => nearBandCutoffProfile.nonneg)
  have hone : nearBandCutoffProfile (0 : ℝ) = 1 :=
    nearBandCutoffProfile.one_of_mem_closedBall (by simp [nearBandCutoffProfile.rIn_pos.le])
  rw [hone]
  norm_num

/-- A fixed actual smooth probability mollifier, rescaled to width `scale`. -/
def transportMollifier (scale value : ℝ) : ℝ :=
  nearBandCutoff scale value / (scale * transportMollifierMass)

theorem contDiff_transportMollifier (scale : ℝ) :
    ContDiff ℝ ∞ (transportMollifier scale) :=
  (contDiff_nearBandCutoff scale).div_const _

theorem transportMollifier_nonneg {scale : ℝ} (hscale : 0 < scale) (value : ℝ) :
    0 ≤ transportMollifier scale value :=
  div_nonneg (nearBandCutoff_nonneg _ _) (mul_pos hscale transportMollifierMass_pos).le

theorem tsupport_transportMollifier_subset {scale : ℝ} (hscale : 0 < scale) :
    tsupport (transportMollifier scale) ⊆ Ioo (-scale) scale := by
  apply subset_trans _ (tsupport_nearBandCutoff_subset hscale)
  apply closure_mono
  intro value hvalue
  rw [Function.mem_support] at hvalue ⊢
  intro hzero
  apply hvalue
  simp only [transportMollifier, hzero, zero_div]

theorem hasCompactSupport_transportMollifier {scale : ℝ} (hscale : 0 < scale) :
    HasCompactSupport (transportMollifier scale) := by
  apply isCompact_Icc.of_isClosed_subset isClosed_closure
  exact (tsupport_transportMollifier_subset hscale).trans Ioo_subset_Icc_self

theorem integrable_transportMollifier {scale : ℝ} (hscale : 0 < scale) :
    Integrable (transportMollifier scale) :=
  (contDiff_transportMollifier scale).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_transportMollifier hscale)

theorem integral_transportMollifier {scale : ℝ} (hscale : 0 < scale) :
    (∫ value : ℝ, transportMollifier scale value) = 1 := by
  unfold transportMollifier nearBandCutoff
  rw [integral_div, Measure.integral_comp_div, abs_of_pos hscale, smul_eq_mul]
  exact div_self (mul_ne_zero hscale.ne' transportMollifierMass_pos.ne')

theorem integral_abs_transportMollifier {scale : ℝ} (hscale : 0 < scale) :
    (∫ value : ℝ, |transportMollifier scale value|) = 1 := by
  calc
    _ = ∫ value : ℝ, transportMollifier scale value :=
      integral_congr_ae (Filter.Eventually.of_forall (fun value =>
        abs_of_nonneg (transportMollifier_nonneg hscale value)))
    _ = 1 := integral_transportMollifier hscale

theorem exists_transportMollifier_derivative_bound :
    ∃ constant : ℝ, 0 < constant ∧ ∀ scale : ℝ, 0 < scale → ∀ value : ℝ,
      |deriv (transportMollifier scale) value| ≤ constant / scale ^ 2 := by
  obtain ⟨constant, hconstant, hbound⟩ := exists_nearBandCutoff_derivative_bound
  refine ⟨constant / transportMollifierMass, div_pos hconstant transportMollifierMass_pos, ?_⟩
  intro scale hscale value
  have hdifferentiable := (contDiff_nearBandCutoff scale).differentiable (by simp)
  rw [show deriv (transportMollifier scale) value =
      deriv (nearBandCutoff scale) value / (scale * transportMollifierMass) from
    (hdifferentiable value).hasDerivAt.div_const _ |>.deriv]
  rw [abs_div, abs_of_pos (mul_pos hscale transportMollifierMass_pos)]
  calc
    _ ≤ (constant / scale) / (scale * transportMollifierMass) :=
      div_le_div_of_nonneg_right (hbound scale hscale value) (mul_pos hscale transportMollifierMass_pos).le
    _ = _ := by field_simp [hscale.ne', transportMollifierMass_pos.ne']

end LambdaCantor.AE
