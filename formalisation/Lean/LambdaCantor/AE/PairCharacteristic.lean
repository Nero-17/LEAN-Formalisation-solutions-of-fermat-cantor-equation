import LambdaCantor.AE.PairFubini
import LambdaCantor.AE.ActualAnnularKernel

noncomputable section
open MeasureTheory Filter
open scoped FourierTransform

namespace LambdaCantor.AE

def samplePairDifference (ratio : ℝ) (sample : ℕ → FourDigits) : ℝ :=
  addressPairDifference (fun index => sample index 0) (fun index => sample index 1)
    (fun index => sample index 2) (fun index => sample index 3) ratio

theorem measurable_samplePairDifference (ratio : ℝ) : Measurable (samplePairDifference ratio) :=
  measurable_sample_addressPairDifference.comp (measurable_id.prodMk measurable_const)

/-- The characteristic function of the actual difference of two self-convolution samples. -/
def pairCharacteristic (ratio frequency : ℝ) : ℂ :=
  ∫ sample, (Real.fourierChar (-(frequency * samplePairDifference ratio sample)) : ℂ)
    ∂fourAddressMeasure

theorem measurable_pairFourierIntegrand (ratio frequency : ℝ) :
    Measurable (fun sampleAndVariable : (ℕ → FourDigits) × ℝ =>
      (Real.fourierChar (-(sampleAndVariable.2 *
        (frequency * samplePairDifference ratio sampleAndVariable.1))) : ℂ)) := by
  have character_continuous : Continuous (fun value : ℝ => (Real.fourierChar value : ℂ)) :=
    continuous_subtype_val.comp Real.continuous_fourierChar
  apply character_continuous.measurable.comp
  exact (measurable_snd.mul (measurable_const.mul
    ((measurable_samplePairDifference ratio).comp measurable_fst))).neg

theorem integrable_pairFourierIntegrand (ratio frequency : ℝ) :
    Integrable (fun sampleAndVariable : (ℕ → FourDigits) × ℝ =>
      complexAnnularCutoff sampleAndVariable.2 *
        (Real.fourierChar (-(sampleAndVariable.2 *
          (frequency * samplePairDifference ratio sampleAndVariable.1))) : ℂ))
      (fourAddressMeasure.prod volume) := by
  apply (integrable_complexAnnularCutoff.comp_snd fourAddressMeasure).mul_bdd
    (measurable_pairFourierIntegrand ratio frequency).aestronglyMeasurable
  exact Eventually.of_forall (fun _ => by simp only [Circle.norm_coe]; exact le_rfl)

/-- The Fourier/probability interchange for the actual four-address residual, with absolute
integrability proved from the constructed cutoff and the unit modulus of the character. -/
theorem expected_fourier_annularCutoff (ratio frequency : ℝ) :
    (∫ sample, 𝓕 complexAnnularCutoff (frequency * samplePairDifference ratio sample)
      ∂fourAddressMeasure) =
    ∫ integrationVariable, complexAnnularCutoff integrationVariable *
      pairCharacteristic ratio (integrationVariable * frequency) := by
  have hfourier (sample : ℕ → FourDigits) :
      𝓕 complexAnnularCutoff (frequency * samplePairDifference ratio sample) =
      ∫ integrationVariable, complexAnnularCutoff integrationVariable *
        (Real.fourierChar (-(integrationVariable * (frequency * samplePairDifference ratio sample))) : ℂ) := by
    simp only [Real.fourier_real_eq, Circle.smul_def, smul_eq_mul]
    congr 1
    ext integrationVariable
    ring
  simp_rw [hfourier]
  rw [integral_integral_swap (integrable_pairFourierIntegrand ratio frequency)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro integrationVariable
  change (∫ sample : ℕ → FourDigits,
      complexAnnularCutoff integrationVariable *
        (Real.fourierChar (-(integrationVariable *
          (frequency * samplePairDifference ratio sample))) : ℂ) ∂fourAddressMeasure) =
    complexAnnularCutoff integrationVariable *
      ∫ sample : ℕ → FourDigits,
        (Real.fourierChar (-((integrationVariable * frequency) *
          samplePairDifference ratio sample)) : ℂ) ∂fourAddressMeasure
  calc
    _ = complexAnnularCutoff integrationVariable *
        ∫ sample : ℕ → FourDigits,
          (Real.fourierChar (-(integrationVariable *
            (frequency * samplePairDifference ratio sample))) : ℂ) ∂fourAddressMeasure :=
      integral_const_mul (μ := fourAddressMeasure) (complexAnnularCutoff integrationVariable)
        (fun sample : ℕ → FourDigits =>
          (Real.fourierChar (-(integrationVariable *
            (frequency * samplePairDifference ratio sample))) : ℂ))
    _ = _ := congrArg (fun value : ℂ => complexAnnularCutoff integrationVariable * value)
      (integral_congr_ae (Eventually.of_forall (fun sample : ℕ → FourDigits =>
        congrArg (fun value : ℝ => (Real.fourierChar (-value) : ℂ))
          (mul_assoc integrationVariable frequency (samplePairDifference ratio sample)).symm)))

end LambdaCantor.AE
