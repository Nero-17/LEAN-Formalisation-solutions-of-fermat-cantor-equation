import LambdaCantor.AE.AddressPairChangeVariables
import LambdaCantor.AE.ScaledCutoff
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory Filter

namespace LambdaCantor.AE

theorem measurable_address_parameter (digits : ℕ → Bool) : Measurable (fun ratio => address ratio digits) := by
  unfold address
  apply (measurable_const.sub measurable_id).mul
  exact Measurable.tsum (fun index => measurable_const.mul (measurable_id.pow_const index))

theorem measurable_addressPairDifference (first second third fourth : ℕ → Bool) :
    Measurable (addressPairDifference first second third fourth) :=
  ((measurable_address_parameter first).add (measurable_address_parameter second)).sub
    ((measurable_address_parameter third).add (measurable_address_parameter fourth))

theorem integrable_addressPairAnnulus_integrand
    (first second third fourth : ℕ → Bool) (parameterCutoff kernel : ℝ → ℝ) (frequency : ℝ)
    {kernelBound : ℝ} (hcutoff : Integrable parameterCutoff volume)
    (hkernelContinuous : Continuous kernel) (hkernelBound : ∀ point, |kernel point| ≤ kernelBound) :
    Integrable (fun ratio => parameterCutoff ratio * frequency *
      kernel (frequency * addressPairDifference first second third fourth ratio)) volume := by
  apply (hcutoff.mul_const frequency).mul_bdd
    (hkernelContinuous.measurable.comp
      (measurable_const.mul (measurable_addressPairDifference first second third fourth))).aestronglyMeasurable
  exact Eventually.of_forall (fun ratio => by
    simpa only [Function.comp_apply, Real.norm_eq_abs] using hkernelBound _)

theorem integrable_addressPair_near_and_off_cutoffs
    (first second third fourth : ℕ → Bool) (parameterCutoff : ℝ → ℝ) (threshold : ℝ)
    (hcutoff : Integrable parameterCutoff volume) :
    Integrable (fun ratio => parameterCutoff ratio *
      nearBandCutoff threshold (addressPairDifference first second third fourth ratio)) volume ∧
    Integrable (fun ratio => parameterCutoff ratio *
      (1 - nearBandCutoff threshold (addressPairDifference first second third fourth ratio))) volume := by
  have hmeasurable := (contDiff_nearBandCutoff threshold).continuous.measurable.comp
    (measurable_addressPairDifference first second third fourth)
  constructor
  · apply hcutoff.mul_bdd hmeasurable.aestronglyMeasurable
    exact Eventually.of_forall (fun ratio => by
      simp only [Function.comp_apply, Real.norm_eq_abs]
      rw [abs_of_nonneg (nearBandCutoff_nonneg _ _)]
      exact nearBandCutoff_le_one _ _)
  · apply hcutoff.mul_bdd (c := 1) (measurable_const.sub hmeasurable).aestronglyMeasurable
    exact Eventually.of_forall (fun ratio => by
      simp only [Pi.sub_apply, Function.comp_apply, Real.norm_eq_abs]
      rw [abs_of_nonneg (sub_nonneg.mpr (nearBandCutoff_le_one _ _))]
      linarith [nearBandCutoff_nonneg threshold (addressPairDifference first second third fourth ratio)])

theorem addressPair_off_cutoff_L1_bound
    (first second third fourth : ℕ → Bool) (parameterCutoff : ℝ → ℝ) (threshold : ℝ)
    (hcutoff : Integrable parameterCutoff volume) :
    (∫ ratio, |parameterCutoff ratio *
      (1 - nearBandCutoff threshold (addressPairDifference first second third fourth ratio))|) ≤
      ∫ ratio, |parameterCutoff ratio| := by
  apply integral_mono
    (integrable_addressPair_near_and_off_cutoffs first second third fourth parameterCutoff threshold hcutoff).2.norm
    hcutoff.norm
  intro ratio
  simp only [Real.norm_eq_abs]
  rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (nearBandCutoff_le_one _ _))]
  have hbound : 1 - nearBandCutoff threshold (addressPairDifference first second third fourth ratio) ≤ 1 := by
    linarith [nearBandCutoff_nonneg threshold (addressPairDifference first second third fourth ratio)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hbound (abs_nonneg (parameterCutoff ratio))

theorem addressPairAnnulus_split_cutoff
    (first second third fourth : ℕ → Bool) (parameterCutoff kernel : ℝ → ℝ) (threshold frequency : ℝ)
    {kernelBound : ℝ} (hcutoff : Integrable parameterCutoff volume)
    (hkernelContinuous : Continuous kernel) (hkernelBound : ∀ point, |kernel point| ≤ kernelBound) :
    addressPairAnnulus parameterCutoff kernel frequency first second third fourth =
      addressPairAnnulus (fun ratio => parameterCutoff ratio *
        nearBandCutoff threshold (addressPairDifference first second third fourth ratio))
        kernel frequency first second third fourth +
      addressPairAnnulus (fun ratio => parameterCutoff ratio *
        (1 - nearBandCutoff threshold (addressPairDifference first second third fourth ratio)))
        kernel frequency first second third fourth := by
  have hcutoffs := integrable_addressPair_near_and_off_cutoffs first second third fourth
    parameterCutoff threshold hcutoff
  unfold addressPairAnnulus
  rw [← integral_add
    (integrable_addressPairAnnulus_integrand first second third fourth _ _ frequency hcutoffs.1 hkernelContinuous hkernelBound)
    (integrable_addressPairAnnulus_integrand first second third fourth _ _ frequency hcutoffs.2 hkernelContinuous hkernelBound)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ratio => by ring)

end LambdaCantor.AE
