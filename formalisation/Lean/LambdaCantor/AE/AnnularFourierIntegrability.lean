import LambdaCantor.AE.AnnularCutoff
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

noncomputable section
open MeasureTheory Filter
open scoped FourierTransform

namespace LambdaCantor.AE

theorem integrable_of_bounded_and_quadratic_decay {function : ℝ → ℝ}
    (hmeasurable : AEStronglyMeasurable function volume)
    {constantZero constantTwo : ℝ}
    (hzero : ∀ value, ‖function value‖ ≤ constantZero)
    (htwo : ∀ value, ‖value‖ ^ 2 * ‖function value‖ ≤ constantTwo) :
    Integrable function := by
  have hmajorant : Integrable (fun value : ℝ =>
      (2 * (constantZero + constantTwo)) * (1 + ‖value‖) ^ (- (2 : ℝ))) :=
    (integrable_one_add_norm (μ := volume) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2)).const_mul _
  apply hmajorant.mono' hmeasurable
  apply Eventually.of_forall
  intro value
  have hdenominator : 0 < (1 + ‖value‖) ^ 2 := by positivity
  have hbound : (1 + ‖value‖) ^ 2 * ‖function value‖ ≤
      2 * (constantZero + constantTwo) := by
    have hnonnegative := mul_nonneg (sq_nonneg (‖value‖ - 1)) (norm_nonneg (function value))
    nlinarith [hzero value, htwo value]
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rw [← div_eq_mul_inv, le_div_iff₀ hdenominator]
  nlinarith

theorem continuous_annularCutoff_fourier : Continuous (𝓕 complexAnnularCutoff) := by
  apply (Real.contDiff_fourier (N := (⊤ : ℕ∞)) _).continuous
  intro order _
  simpa only [norm_iteratedFDeriv_zero] using
    integrable_annularCutoff_derivative_moment order 0

/-- Every absolute moment of the actual transformed cutoff is integrable, obtained directly
from two of the explicit decay estimates and an integrable rational majorant. -/
theorem integrable_annularCutoff_fourier_moment (power : ℕ) :
    Integrable (fun frequency : ℝ => ‖frequency‖ ^ power *
      ‖𝓕 complexAnnularCutoff frequency‖) := by
  refine integrable_of_bounded_and_quadratic_decay
    (function := fun frequency : ℝ => ‖frequency‖ ^ power * ‖𝓕 complexAnnularCutoff frequency‖)
    (constantZero := 2 ^ power *
      ∑ derivative ∈ Finset.range 1 ×ˢ Finset.range (power + 1),
        ∫ value : ℝ, ‖value‖ ^ derivative.1 *
          ‖iteratedFDeriv ℝ derivative.2 complexAnnularCutoff value‖)
    (constantTwo := 2 ^ (power + 2) *
      ∑ derivative ∈ Finset.range 1 ×ˢ Finset.range (power + 2 + 1),
        ∫ value : ℝ, ‖value‖ ^ derivative.1 *
          ‖iteratedFDeriv ℝ derivative.2 complexAnnularCutoff value‖) ?_ ?_ ?_
  · exact (((continuous_norm.pow power).mul continuous_annularCutoff_fourier.norm).congr
      (fun frequency => rfl)).aestronglyMeasurable
  · intro frequency
    simpa only [norm_mul, norm_pow, norm_norm] using
      annularCutoff_fourier_decay power frequency
  · intro frequency
    simpa only [norm_mul, norm_pow, norm_norm, ← mul_assoc, ← pow_add, Nat.add_comm 2 power]
      using annularCutoff_fourier_decay (power + 2) frequency

theorem integrable_annularCutoff_fourier : Integrable (𝓕 complexAnnularCutoff) := by
  have hnorm : Integrable (fun frequency : ℝ => ‖𝓕 complexAnnularCutoff frequency‖) := by
    simpa only [pow_zero, one_mul] using integrable_annularCutoff_fourier_moment 0
  exact hnorm.mono continuous_annularCutoff_fourier.aestronglyMeasurable
    (Eventually.of_forall (fun _ => by simp))

/-- The zero-mean assertion now follows from inversion for the particular annular cutoff. -/
theorem integral_annularCutoff_inverseFourier :
    (∫ value : ℝ, 𝓕⁻ complexAnnularCutoff value) = 0 := by
  have hinversion := integrable_complexAnnularCutoff.fourier_fourierInv_eq
    integrable_annularCutoff_fourier contDiff_complexAnnularCutoff.continuous.continuousAt
    (v := (0 : ℝ))
  have hzero : complexAnnularCutoff 0 = 0 := by
    simp only [complexAnnularCutoff, annularCutoff_zero_near_origin (by norm_num : |(0 : ℝ)| ≤ 1 / 4),
      Complex.ofReal_zero]
  simpa [Real.fourier_real_eq_integral_exp_smul, hzero] using hinversion

end LambdaCantor.AE
