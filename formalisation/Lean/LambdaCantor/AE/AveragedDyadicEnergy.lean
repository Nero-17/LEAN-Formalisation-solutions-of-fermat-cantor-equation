import LambdaCantor.AE.AnnularEnergyIdentity

noncomputable section
open MeasureTheory Set

namespace LambdaCantor.AE

/-- The actual averaged Fourier-annulus energy, with the frequency Jacobian included. -/
def averagedAnnularEnergy (parameterCutoff : ℝ → ℝ) (frequency : ℝ) : ℝ :=
  ∫ ratio, parameterCutoff ratio * frequency * annularEnergy ratio frequency

theorem averagedAnnularEnergy_le_expectedAbsolute (parameterCutoff : ℝ → ℝ)
    (hcutoff : Integrable parameterCutoff) (frequency : ℝ) :
    averagedAnnularEnergy parameterCutoff frequency ≤
      expectedAbsoluteAnnulus parameterCutoff frequency := by
  unfold averagedAnnularEnergy
  rw [← expected_annulus_eq_parameter_energy parameterCutoff hcutoff frequency]
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs, expectedAbsoluteAnnulus] using
      norm_integral_le_integral_norm (fun sample : ℕ → FourDigits =>
        addressPairAnnulus parameterCutoff annularKernel frequency
          (fun index => sample index 0) (fun index => sample index 1)
          (fun index => sample index 2) (fun index => sample index 3)))

theorem averagedAnnularEnergy_nonneg (parameterCutoff : ℝ → ℝ)
    (hcutoff : ∀ ratio, 0 ≤ parameterCutoff ratio) {frequency : ℝ} (hfrequency : 0 ≤ frequency) :
    0 ≤ averagedAnnularEnergy parameterCutoff frequency :=
  integral_nonneg (fun ratio => mul_nonneg (mul_nonneg (hcutoff ratio) hfrequency)
    (annularEnergy_nonneg ratio frequency))

/-- Averaged dyadic Fourier energy for the actual Cantor self-convolution is summable
throughout the strict exponent range. All kernel, product-law and Fubini inputs have been
constructed in the preceding modules, and no analytic estimate is assumed here. -/
theorem summable_averaged_dyadic_energy
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1)
    (parameterCutoff : ℝ → ℝ) (hsmooth : ContDiff ℝ 1 parameterCutoff)
    (hcompact : HasCompactSupport parameterCutoff)
    (hsupport : tsupport parameterCutoff ⊆ Ioo lower upper)
    (hnonnegative : ∀ ratio, 0 ≤ parameterCutoff ratio) :
    Summable (fun scale : ℕ => ((2 : ℝ) ^ scale) ^ (2 * regularity) *
      averagedAnnularEnergy parameterCutoff ((2 : ℝ) ^ scale)) := by
  apply Summable.of_nonneg_of_le _ _
    (summable_actual_weighted_annuli hlower horder hupper hregularity hrange
      parameterCutoff hsmooth hcompact hsupport)
  · intro scale
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (averagedAnnularEnergy_nonneg parameterCutoff hnonnegative (by positivity))
  · intro scale
    exact mul_le_mul_of_nonneg_left
      (averagedAnnularEnergy_le_expectedAbsolute parameterCutoff
        (hsmooth.continuous.integrable_of_hasCompactSupport hcompact) _)
      (Real.rpow_nonneg (by positivity) _)

end LambdaCantor.AE
