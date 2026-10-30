import LambdaCantor.AE.ScaledCutoff
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

open Set MeasureTheory
open scoped ContDiff FourierTransform

namespace LambdaCantor.AE

/-- A nonnegative smooth annular cutoff, equal to one on 1 ≤ |frequency| ≤ 2. -/
def annularCutoff (frequency : ℝ) : ℝ :=
  nearBandCutoff 8 frequency * (1 - nearBandCutoff 1 frequency)

theorem contDiff_annularCutoff : ContDiff ℝ ∞ annularCutoff :=
  (contDiff_nearBandCutoff 8).mul (contDiff_const.sub (contDiff_nearBandCutoff 1))

theorem annularCutoff_nonneg (frequency : ℝ) : 0 ≤ annularCutoff frequency :=
  mul_nonneg (nearBandCutoff_nonneg _ _) (sub_nonneg.mpr (nearBandCutoff_le_one _ _))

theorem annularCutoff_even (frequency : ℝ) :
    annularCutoff (-frequency) = annularCutoff frequency := by
  simp only [annularCutoff, nearBandCutoff, neg_div, nearBandCutoffProfile.neg]

theorem annularCutoff_zero_near_origin {frequency : ℝ} (hfrequency : |frequency| ≤ 1 / 4) :
    annularCutoff frequency = 0 := by
  rw [annularCutoff, nearBandCutoff_eq_one (by norm_num : (0 : ℝ) < 1)
    (by simpa using hfrequency)]
  simp

theorem annularCutoff_eq_one {frequency : ℝ}
    (hlower : 1 ≤ |frequency|) (hupper : |frequency| ≤ 2) :
    annularCutoff frequency = 1 := by
  have houter : nearBandCutoff 8 frequency = 1 :=
    nearBandCutoff_eq_one (by norm_num) (by norm_num; exact hupper)
  have hinner : nearBandCutoff 1 frequency = 0 := by
    apply nearBandCutoffProfile.zero_of_le_dist
    change (1 / 2 : ℝ) ≤ dist (frequency / 1) 0
    simpa only [div_one, Real.dist_eq, sub_zero] using
      (show (1 / 2 : ℝ) ≤ |frequency| by linarith)
  simp [annularCutoff, houter, hinner]

theorem hasCompactSupport_annularCutoff : HasCompactSupport annularCutoff := by
  have hcompact : HasCompactSupport (nearBandCutoff 8) := by
    apply isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) 
    intro frequency hfrequency
    have hband := tsupport_nearBandCutoff_subset (by norm_num : (0 : ℝ) < 8) hfrequency
    exact ⟨hband.1.le, hband.2.le⟩
  exact hcompact.mul_right

def complexAnnularCutoff (frequency : ℝ) : ℂ := annularCutoff frequency

theorem contDiff_complexAnnularCutoff : ContDiff ℝ ∞ complexAnnularCutoff :=
  Complex.ofRealCLM.contDiff.comp contDiff_annularCutoff

theorem hasCompactSupport_complexAnnularCutoff : HasCompactSupport complexAnnularCutoff :=
  hasCompactSupport_annularCutoff.comp_left Complex.ofReal_zero

theorem integrable_complexAnnularCutoff : Integrable complexAnnularCutoff :=
  contDiff_complexAnnularCutoff.continuous.integrable_of_hasCompactSupport
    hasCompactSupport_complexAnnularCutoff

/-- All derivative moments needed by the cached Fourier decay theorem are integrable. -/
theorem integrable_annularCutoff_derivative_moment (power order : ℕ) :
    Integrable (fun frequency : ℝ => ‖frequency‖ ^ power *
      ‖iteratedFDeriv ℝ order complexAnnularCutoff frequency‖) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_norm.pow power).mul
      ((contDiff_complexAnnularCutoff.continuous_iteratedFDeriv
        (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm)
  · exact ((hasCompactSupport_complexAnnularCutoff.iteratedFDeriv order).norm).mul_left

/-- Quantitative polynomial decay of the actual Fourier transform, without a Schwartz-space
dependency. The displayed finite sum consists only of integrals of the constructed cutoff. -/
theorem annularCutoff_fourier_decay (order : ℕ) (frequency : ℝ) :
    ‖frequency‖ ^ order * ‖𝓕 complexAnnularCutoff frequency‖ ≤
      2 ^ order * ∑ derivative ∈ Finset.range 1 ×ˢ Finset.range (order + 1),
        ∫ value : ℝ, ‖value‖ ^ derivative.1 *
          ‖iteratedFDeriv ℝ derivative.2 complexAnnularCutoff value‖ := by
  simpa only [norm_iteratedFDeriv_zero, pow_zero, Nat.cast_zero, mul_zero, zero_add, one_mul] using
    (Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := (⊤ : ℕ∞)) (N := (⊤ : ℕ∞))
      contDiff_complexAnnularCutoff
      (fun power derivative _ _ => integrable_annularCutoff_derivative_moment power derivative)
      (k := 0) (n := order) (by simp) (by simp) frequency)

end LambdaCantor.AE
