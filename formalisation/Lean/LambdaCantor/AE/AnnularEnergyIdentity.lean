import LambdaCantor.AE.CharacteristicFactorization
import LambdaCantor.AE.StochasticAnnulusSummation

noncomputable section
open MeasureTheory Filter
open scoped FourierTransform

namespace LambdaCantor.AE

def annularEnergy (ratio frequency : ℝ) : ℝ :=
  ∫ integrationVariable : ℝ, annularCutoff integrationVariable * ‖addressFourier ratio (integrationVariable * frequency)‖ ^ 4

theorem annularEnergy_nonneg (ratio frequency : ℝ) : 0 ≤ annularEnergy ratio frequency :=
  integral_nonneg (fun integrationVariable => mul_nonneg (annularCutoff_nonneg integrationVariable) (by positivity))

theorem integrable_annularEnergy_integrand (ratio frequency : ℝ) :
    Integrable (fun integrationVariable : ℝ => (annularCutoff integrationVariable : ℂ) *
      (‖addressFourier ratio (integrationVariable * frequency)‖ ^ 4 : ℝ)) := by
  have hintegrable := (integrable_pairFourierIntegrand ratio frequency).integral_prod_right
  apply hintegrable.congr
  exact Eventually.of_forall (fun integrationVariable => by
    change (∫ sample : ℕ → FourDigits, complexAnnularCutoff integrationVariable *
        (Real.fourierChar (-(integrationVariable *
          (frequency * samplePairDifference ratio sample))) : ℂ) ∂fourAddressMeasure) =
      (annularCutoff integrationVariable : ℂ) *
        (‖addressFourier ratio (integrationVariable * frequency)‖ ^ 4 : ℝ)
    calc
      _ = complexAnnularCutoff integrationVariable *
          ∫ sample : ℕ → FourDigits,
            (Real.fourierChar (-(integrationVariable *
              (frequency * samplePairDifference ratio sample))) : ℂ) ∂fourAddressMeasure :=
        integral_const_mul (μ := fourAddressMeasure) (complexAnnularCutoff integrationVariable) _
      _ = complexAnnularCutoff integrationVariable *
          pairCharacteristic ratio (integrationVariable * frequency) :=
        congrArg (fun value : ℂ => complexAnnularCutoff integrationVariable * value)
          (integral_congr_ae (Eventually.of_forall (fun sample : ℕ → FourDigits =>
            congrArg (fun value : ℝ => (Real.fourierChar (-value) : ℂ))
              (mul_assoc integrationVariable frequency (samplePairDifference ratio sample)).symm)))
      _ = _ := congrArg (fun value : ℂ => (annularCutoff integrationVariable : ℂ) * value)
        (pairCharacteristic_eq_fourth_power ratio (integrationVariable * frequency)))

theorem integrable_sample_fourierCutoff (ratio frequency : ℝ) :
    Integrable (fun sample => 𝓕 complexAnnularCutoff
      (frequency * samplePairDifference ratio sample)) fourAddressMeasure := by
  have hintegrable := (integrable_pairFourierIntegrand ratio frequency).integral_prod_left
  convert hintegrable using 1
  ext sample
  simp only [Real.fourier_real_eq, Circle.smul_def, smul_eq_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => by ring)

theorem expected_real_fourierCutoff (ratio frequency : ℝ) :
    (∫ sample, (𝓕 complexAnnularCutoff
      (frequency * samplePairDifference ratio sample)).re ∂fourAddressMeasure) =
      annularEnergy ratio frequency := by
  calc
    _ = (∫ sample, 𝓕 complexAnnularCutoff
        (frequency * samplePairDifference ratio sample) ∂fourAddressMeasure).re := by
      simpa only [Complex.reCLM_apply] using
        Complex.reCLM.integral_comp_comm (integrable_sample_fourierCutoff ratio frequency)
    _ = (∫ integrationVariable : ℝ, (annularCutoff integrationVariable : ℂ) *
        (‖addressFourier ratio (integrationVariable * frequency)‖ ^ 4 : ℝ)).re :=
      congrArg Complex.re (expected_fourier_annularCutoff_eq_fourth_power ratio frequency)
    _ = ∫ integrationVariable : ℝ, ((annularCutoff integrationVariable : ℂ) *
        (‖addressFourier ratio (integrationVariable * frequency)‖ ^ 4 : ℝ)).re := by
      simpa only [Complex.reCLM_apply] using
        (Complex.reCLM.integral_comp_comm (integrable_annularEnergy_integrand ratio frequency)).symm
    _ = _ := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        annularEnergy]

theorem annularEnergy_neg (ratio frequency : ℝ) :
    annularEnergy ratio (-frequency) = annularEnergy ratio frequency := by
  unfold annularEnergy
  simp only [mul_neg, addressFourier_neg, Complex.norm_conj]

/-- Exact real-kernel energy identity for the constructed cutoff and actual Bernoulli address law. -/
theorem expected_annularKernel_eq_energy (ratio frequency : ℝ) :
    (∫ sample, annularKernel (frequency * samplePairDifference ratio sample)
      ∂fourAddressMeasure) = annularEnergy ratio frequency := by
  have hpositive : Integrable (fun sample : ℕ → FourDigits =>
      (𝓕 complexAnnularCutoff (frequency * samplePairDifference ratio sample)).re)
      fourAddressMeasure :=
    Complex.reCLM.integrable_comp (integrable_sample_fourierCutoff ratio frequency)
  have hnegative : Integrable (fun sample : ℕ → FourDigits =>
      (𝓕 complexAnnularCutoff (-(frequency * samplePairDifference ratio sample))).re)
      fourAddressMeasure := by
    have hcomplex : Integrable (fun sample : ℕ → FourDigits =>
        𝓕 complexAnnularCutoff (-(frequency * samplePairDifference ratio sample)))
        fourAddressMeasure := by
      simpa only [neg_mul] using integrable_sample_fourierCutoff ratio (-frequency)
    exact Complex.reCLM.integrable_comp hcomplex
  have hnegativeIntegral : (∫ sample : ℕ → FourDigits,
      (𝓕 complexAnnularCutoff (-(frequency * samplePairDifference ratio sample))).re
      ∂fourAddressMeasure) = annularEnergy ratio (-frequency) := by
    simpa only [neg_mul] using expected_real_fourierCutoff ratio (-frequency)
  unfold annularKernel
  rw [integral_div, integral_add hpositive hnegative,
    expected_real_fourierCutoff, hnegativeIntegral, annularEnergy_neg]
  ring

theorem expected_annulus_eq_parameter_energy (parameterCutoff : ℝ → ℝ)
    (hcutoff : Integrable parameterCutoff) (frequency : ℝ) :
    (∫ sample, addressPairAnnulus parameterCutoff annularKernel frequency
      (fun index => sample index 0) (fun index => sample index 1)
      (fun index => sample index 2) (fun index => sample index 3) ∂fourAddressMeasure) =
    ∫ ratio, parameterCutoff ratio * frequency * annularEnergy ratio frequency := by
  obtain ⟨bound, hbound⟩ := annularKernel_pairwise_hypotheses.2.2.2.2.1
  rw [integral_addressPairAnnulus_eq parameterCutoff annularKernel frequency bound
    hcutoff continuous_annularKernel hbound]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ratio =>
    congrArg (fun value : ℝ => parameterCutoff ratio * frequency * value)
      (expected_annularKernel_eq_energy ratio frequency))

end LambdaCantor.AE
