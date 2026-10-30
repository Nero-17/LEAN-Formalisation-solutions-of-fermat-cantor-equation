import LambdaCantor.AE.AveragedDyadicEnergy

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace LambdaCantor.AE

theorem integrable_parameter_annularEnergy (parameterCutoff : ℝ → ℝ)
    (hcutoff : Integrable parameterCutoff) (frequency : ℝ) :
    Integrable (fun ratio => parameterCutoff ratio * frequency * annularEnergy ratio frequency) := by
  obtain ⟨bound, hbound⟩ := annularKernel_pairwise_hypotheses.2.2.2.2.1
  have hintegrable := (integrable_sample_parameter_kernel parameterCutoff annularKernel frequency bound
    hcutoff continuous_annularKernel hbound).integral_prod_right
  apply hintegrable.congr
  exact Eventually.of_forall (fun ratio => by
    change (∫ sample : ℕ → FourDigits, parameterCutoff ratio * frequency *
        annularKernel (frequency * samplePairDifference ratio sample) ∂fourAddressMeasure) =
      parameterCutoff ratio * frequency * annularEnergy ratio frequency
    exact (integral_const_mul (μ := fourAddressMeasure) (parameterCutoff ratio * frequency)
      (fun sample : ℕ → FourDigits => annularKernel (frequency * samplePairDifference ratio sample))).trans
      (congrArg (fun value : ℝ => parameterCutoff ratio * frequency * value)
        (expected_annularKernel_eq_energy ratio frequency)))

/-- Tonelli converts the actual averaged dyadic estimate into almost-everywhere finite
weighted energy. The cutoff remains explicit, so the conclusion applies wherever it is positive. -/
theorem lintegral_cutoff_dyadic_energy_ne_top
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1)
    (parameterCutoff : ℝ → ℝ) (hsmooth : ContDiff ℝ 1 parameterCutoff)
    (hcompact : HasCompactSupport parameterCutoff)
    (hsupport : tsupport parameterCutoff ⊆ Set.Ioo lower upper)
    (hnonnegative : ∀ ratio, 0 ≤ parameterCutoff ratio) :
    (∫⁻ ratio : ℝ, ∑' scale : ℕ, ENNReal.ofReal
      (((2 : ℝ) ^ scale) ^ (2 * regularity) *
        (parameterCutoff ratio * (2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale)))) ≠ ∞ := by
  have hintegrable (scale : ℕ) : Integrable (fun ratio =>
      ((2 : ℝ) ^ scale) ^ (2 * regularity) *
        (parameterCutoff ratio * (2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale))) :=
    (integrable_parameter_annularEnergy parameterCutoff
      (hsmooth.continuous.integrable_of_hasCompactSupport hcompact) _).const_mul _
  have hnonneg (scale : ℕ) (ratio : ℝ) : 0 ≤
      ((2 : ℝ) ^ scale) ^ (2 * regularity) *
        (parameterCutoff ratio * (2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale)) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (mul_nonneg (mul_nonneg (hnonnegative ratio) (by positivity)) (annularEnergy_nonneg _ _))
  rw [lintegral_tsum (fun scale => (hintegrable scale).aemeasurable.ennreal_ofReal)]
  simp_rw [← ofReal_integral_eq_lintegral_ofReal (hintegrable _)
    (Eventually.of_forall (hnonneg _)), integral_const_mul]
  exact (summable_averaged_dyadic_energy hlower horder hupper hregularity hrange
    parameterCutoff hsmooth hcompact hsupport hnonnegative).tsum_ofReal_ne_top

theorem ae_finite_cutoff_dyadic_energy
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1)
    (parameterCutoff : ℝ → ℝ) (hsmooth : ContDiff ℝ 1 parameterCutoff)
    (hcompact : HasCompactSupport parameterCutoff)
    (hsupport : tsupport parameterCutoff ⊆ Set.Ioo lower upper)
    (hnonnegative : ∀ ratio, 0 ≤ parameterCutoff ratio) :
    ∀ᵐ ratio : ℝ, ∑' scale : ℕ, ENNReal.ofReal
      (((2 : ℝ) ^ scale) ^ (2 * regularity) *
        (parameterCutoff ratio * (2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale))) < ∞ := by
  have hintegrable (scale : ℕ) : Integrable (fun ratio =>
      ((2 : ℝ) ^ scale) ^ (2 * regularity) *
        (parameterCutoff ratio * (2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale))) :=
    (integrable_parameter_annularEnergy parameterCutoff
      (hsmooth.continuous.integrable_of_hasCompactSupport hcompact) _).const_mul _
  have hnonneg (scale : ℕ) (ratio : ℝ) : 0 ≤
      ((2 : ℝ) ^ scale) ^ (2 * regularity) *
        (parameterCutoff ratio * (2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale)) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (mul_nonneg (mul_nonneg (hnonnegative ratio) (by positivity)) (annularEnergy_nonneg _ _))
  apply ae_lt_top' (AEMeasurable.tsum (fun scale => (hintegrable scale).aemeasurable.ennreal_ofReal))
  rw [lintegral_tsum (fun scale => (hintegrable scale).aemeasurable.ennreal_ofReal)]
  simp_rw [← ofReal_integral_eq_lintegral_ofReal (hintegrable _)
    (Eventually.of_forall (hnonneg _)), integral_const_mul]
  exact (summable_averaged_dyadic_energy hlower horder hupper hregularity hrange
    parameterCutoff hsmooth hcompact hsupport hnonnegative).tsum_ofReal_ne_top

theorem ae_finite_dyadic_energy_on_positive_cutoff
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1)
    (parameterCutoff : ℝ → ℝ) (hsmooth : ContDiff ℝ 1 parameterCutoff)
    (hcompact : HasCompactSupport parameterCutoff)
    (hsupport : tsupport parameterCutoff ⊆ Set.Ioo lower upper)
    (hnonnegative : ∀ ratio, 0 ≤ parameterCutoff ratio) :
    ∀ᵐ ratio : ℝ, 0 < parameterCutoff ratio →
      ∑' scale : ℕ, ENNReal.ofReal
        (((2 : ℝ) ^ scale) ^ (2 * regularity) *
          ((2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale))) < ∞ := by
  filter_upwards [ae_finite_cutoff_dyadic_energy hlower horder hupper hregularity hrange
    parameterCutoff hsmooth hcompact hsupport hnonnegative] with ratio hfinite
  intro hpositive
  have hidentity (scale : ℕ) :
      ((2 : ℝ) ^ scale) ^ (2 * regularity) *
        (parameterCutoff ratio * (2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale)) =
      parameterCutoff ratio * (((2 : ℝ) ^ scale) ^ (2 * regularity) *
        ((2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale))) := by ring
  simp_rw [hidentity, ENNReal.ofReal_mul hpositive.le, ENNReal.tsum_mul_left] at hfinite
  by_contra hnotfinite
  have htop : (∑' scale : ℕ, ENNReal.ofReal
      (((2 : ℝ) ^ scale) ^ (2 * regularity) *
        ((2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale)))) = ∞ :=
    top_le_iff.mp (le_of_not_gt hnotfinite)
  rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hpositive).ne'] at hfinite
  exact (lt_irrefl _ hfinite)

end LambdaCantor.AE
