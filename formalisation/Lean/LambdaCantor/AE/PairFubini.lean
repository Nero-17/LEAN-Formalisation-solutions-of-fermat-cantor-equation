import LambdaCantor.AE.PairProbability
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Filter

namespace LambdaCantor.AE

theorem measurable_sample_address (column : Fin 4) :
    Measurable (fun sampleAndRatio : (ℕ → FourDigits) × ℝ =>
      address sampleAndRatio.2 (fun index => sampleAndRatio.1 index column)) := by
  unfold address
  apply (measurable_const.sub measurable_snd).mul
  apply Measurable.tsum
  intro index
  apply Measurable.mul _ (measurable_snd.pow_const index)
  exact (measurable_of_countable (fun digit : Bool => if digit then (1 : ℝ) else 0)).comp
    ((measurable_pi_apply column).comp ((measurable_pi_apply index).comp measurable_fst))

theorem measurable_sample_addressPairDifference :
    Measurable (fun sampleAndRatio : (ℕ → FourDigits) × ℝ =>
      addressPairDifference (fun index => sampleAndRatio.1 index 0)
        (fun index => sampleAndRatio.1 index 1) (fun index => sampleAndRatio.1 index 2)
        (fun index => sampleAndRatio.1 index 3) sampleAndRatio.2) :=
  ((measurable_sample_address 0).add (measurable_sample_address 1)).sub
    ((measurable_sample_address 2).add (measurable_sample_address 3))

/-- Absolute integrability on the actual probability-parameter product. -/
theorem integrable_sample_parameter_kernel (parameterCutoff kernel : ℝ → ℝ)
    (frequency kernelBound : ℝ) (hcutoff : Integrable parameterCutoff)
    (hkernel : Continuous kernel) (hbound : ∀ value, |kernel value| ≤ kernelBound) :
    Integrable (fun sampleAndRatio : (ℕ → FourDigits) × ℝ =>
      parameterCutoff sampleAndRatio.2 * frequency * kernel (frequency *
        addressPairDifference (fun index => sampleAndRatio.1 index 0)
          (fun index => sampleAndRatio.1 index 1) (fun index => sampleAndRatio.1 index 2)
          (fun index => sampleAndRatio.1 index 3) sampleAndRatio.2))
      (fourAddressMeasure.prod volume) := by
  apply ((hcutoff.comp_snd fourAddressMeasure).mul_const frequency).mul_bdd
    (hkernel.measurable.comp
      (measurable_const.mul measurable_sample_addressPairDifference)).aestronglyMeasurable
  exact Eventually.of_forall (fun _ => by
    simpa only [Function.comp_apply, Real.norm_eq_abs] using hbound _)

/-- Fubini connects the actual expected pair-annulus estimate to the parameter-wise
average kernel; no product-integrability assumption is left to the caller. -/
theorem integral_addressPairAnnulus_eq (parameterCutoff kernel : ℝ → ℝ)
    (frequency kernelBound : ℝ) (hcutoff : Integrable parameterCutoff)
    (hkernel : Continuous kernel) (hbound : ∀ value, |kernel value| ≤ kernelBound) :
    (∫ sample, addressPairAnnulus parameterCutoff kernel frequency
      (fun index => sample index 0) (fun index => sample index 1)
      (fun index => sample index 2) (fun index => sample index 3) ∂fourAddressMeasure) =
    ∫ ratio, parameterCutoff ratio * frequency *
      ∫ sample, kernel (frequency * addressPairDifference
        (fun index => sample index 0) (fun index => sample index 1)
        (fun index => sample index 2) (fun index => sample index 3) ratio) ∂fourAddressMeasure := by
  unfold addressPairAnnulus
  rw [integral_integral_swap
    (integrable_sample_parameter_kernel parameterCutoff kernel frequency kernelBound
      hcutoff hkernel hbound)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ratio => integral_const_mul _ _)

end LambdaCantor.AE
