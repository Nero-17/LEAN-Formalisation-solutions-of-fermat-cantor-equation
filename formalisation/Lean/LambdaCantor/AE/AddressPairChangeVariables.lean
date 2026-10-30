import LambdaCantor.AE.AddressPairExtendedDensity
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open Set Filter MeasureTheory
open scoped NNReal

namespace LambdaCantor.AE

/-- The actual near-band parameter integral equals the integral against the
zero-extended inverse density. The Jacobian theorem is applied to the actual
address residual on its proved injective band. -/
theorem addressPairAnnulus_cutoff_change_variables
    (first second third fourth : ℕ → Bool) {lower upper band : ℝ}
    (parameterCutoff valueCutoff kernel : ℝ → ℝ) (frequency : ℝ)
    (hband : 0 < band)
    (hdifferentiable : ∀ ratio ∈ Ioo lower upper,
      DifferentiableAt ℝ (addressPairDifference first second third fourth) ratio)
    (hnegative : ∀ ratio ∈ Ioo lower upper,
      |addressPairDifference first second third fourth ratio| < band →
        deriv (addressPairDifference first second third fourth) ratio < 0)
    (hparameterSupport : ∀ ratio, ratio ∉ Ioo lower upper → parameterCutoff ratio = 0)
    (hvalueSupport : ∀ value, value ∉ Ioo (-band) band → valueCutoff value = 0) :
    addressPairAnnulus
      (fun ratio => parameterCutoff ratio *
        valueCutoff (addressPairDifference first second third fourth ratio))
      kernel frequency first second third fourth =
    ∫ value, frequency * kernel (frequency * value) *
      addressPairExtendedDensity first second third fourth lower upper band parameterCutoff valueCutoff value := by
  have hbandMeasurable :=
    (isOpen_addressPairBand first second third fourth (band := band) hdifferentiable).measurableSet
  have himageMeasurable := (isOpen_addressPairBand_image first second third fourth hband
    hdifferentiable hnegative).measurableSet
  have hanti := strictAntiOn_of_deriv_neg_on_band (convex_Ioo lower upper) hband
    hdifferentiable hnegative
  have hleftInverse : ∀ ratio ∈ addressPairBand first second third fourth lower upper band,
      addressPairInverse first second third fourth lower upper band
        (addressPairDifference first second third fourth ratio) = ratio :=
    fun ratio hratio => hanti.injOn.leftInvOn_invFunOn hratio
  have hparameterIntegral : addressPairAnnulus
      (fun ratio => parameterCutoff ratio * valueCutoff (addressPairDifference first second third fourth ratio))
      kernel frequency first second third fourth =
      ∫ ratio in addressPairBand first second third fourth lower upper band,
        parameterCutoff ratio * valueCutoff (addressPairDifference first second third fourth ratio) *
          frequency * kernel (frequency * addressPairDifference first second third fourth ratio) := by
    rw [← integral_indicator hbandMeasurable]
    unfold addressPairAnnulus
    apply integral_congr_ae
    filter_upwards [] with ratio
    by_cases hratio : ratio ∈ addressPairBand first second third fourth lower upper band
    · rw [indicator_of_mem hratio]
    · rw [indicator_of_notMem hratio]
      by_cases hparameter : ratio ∈ Ioo lower upper
      · have hvalue : addressPairDifference first second third fourth ratio ∉ Ioo (-band) band :=
          fun h => hratio ⟨hparameter, h⟩
        simp only [hvalueSupport _ hvalue, mul_zero, zero_mul]
      · simp only [hparameterSupport ratio hparameter, zero_mul]
  have hsubstitution := integral_image_eq_integral_abs_deriv_smul hbandMeasurable
    (fun ratio hratio => (hdifferentiable ratio hratio.1).hasDerivAt.hasDerivWithinAt)
    hanti.injOn
    (fun value => frequency * kernel (frequency * value) *
      addressPairInverseDensity first second third fourth lower upper band parameterCutoff valueCutoff value)
  have hjacobian :
      (∫ ratio in addressPairBand first second third fourth lower upper band,
        |deriv (addressPairDifference first second third fourth) ratio| •
          (frequency * kernel (frequency * addressPairDifference first second third fourth ratio) *
            addressPairInverseDensity first second third fourth lower upper band parameterCutoff valueCutoff
              (addressPairDifference first second third fourth ratio))) =
      ∫ ratio in addressPairBand first second third fourth lower upper band,
        parameterCutoff ratio * valueCutoff (addressPairDifference first second third fourth ratio) *
          frequency * kernel (frequency * addressPairDifference first second third fourth ratio) := by
    apply setIntegral_congr_fun hbandMeasurable
    intro ratio hratio
    have hsign := hnegative ratio hratio.1 (abs_lt.mpr hratio.2)
    simp only [addressPairInverseDensity, hleftInverse ratio hratio,
      smul_eq_mul, abs_of_neg hsign]
    field_simp [ne_of_lt hsign]
    <;> ring
  have hextended :
      (∫ value, frequency * kernel (frequency * value) *
        addressPairExtendedDensity first second third fourth lower upper band parameterCutoff valueCutoff value) =
      ∫ value in addressPairDifference first second third fourth ''
          addressPairBand first second third fourth lower upper band,
        frequency * kernel (frequency * value) *
          addressPairInverseDensity first second third fourth lower upper band parameterCutoff valueCutoff value := by
    rw [← integral_indicator himageMeasurable]
    apply integral_congr_ae
    filter_upwards [] with value
    by_cases hvalue : value ∈ addressPairDifference first second third fourth ''
        addressPairBand first second third fourth lower upper band
    · simp only [addressPairExtendedDensity, indicator_of_mem hvalue]
    · simp only [addressPairExtendedDensity, indicator_of_notMem hvalue, mul_zero]
  exact hparameterIntegral.trans (hjacobian.symm.trans (hsubstitution.symm.trans hextended.symm))

/-- Rescaling the image variable gives exactly the zero-mean-kernel
integral used in the cancellation estimate, including all frequency factors. -/
theorem integral_scaled_addressPairExtendedDensity
    (first second third fourth : ℕ → Bool) (lower upper band : ℝ)
    (parameterCutoff valueCutoff kernel : ℝ → ℝ) {frequency : ℝ} (hfrequency : 0 < frequency) :
    (∫ value, frequency * kernel (frequency * value) *
      addressPairExtendedDensity first second third fourth lower upper band parameterCutoff valueCutoff value) =
    ∫ point, kernel point * addressPairExtendedDensity first second third fourth lower upper band
      parameterCutoff valueCutoff (point / frequency) := by
  calc
    _ = frequency * ∫ value,
        kernel (frequency * value) * addressPairExtendedDensity first second third fourth lower upper band
          parameterCutoff valueCutoff ((frequency * value) / frequency) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with value
      simp only [mul_div_cancel_left₀ value (ne_of_gt hfrequency)]
      ring
    _ = _ := by
      rw [Measure.integral_comp_mul_left
        (fun point : ℝ => kernel point *
          addressPairExtendedDensity first second third fourth lower upper band
            parameterCutoff valueCutoff (point / frequency)) frequency]
      simp only [smul_eq_mul, abs_of_pos (inv_pos.mpr hfrequency), ← mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hfrequency), one_mul]

/-- The near-band part of the manuscript's pair-annulus estimate, now for
the original parameter integral. Both the change of variables and the
zero-extension at image boundaries are discharged by preceding theorems.
The remaining analytic input is the local derivative estimate for the
explicit inverse density, plus the kernel's integrability and zero mean. -/
theorem addressPairAnnulus_near_band_bound
    (first second third fourth : ℕ → Bool) {lower upper band frequency : ℝ}
    (parameterCutoff valueCutoff kernel : ℝ → ℝ) (constant : ℝ≥0)
    (hband : 0 < band) (hfrequency : 0 < frequency)
    (hdifferentiable : ∀ ratio ∈ Ioo lower upper,
      DifferentiableAt ℝ (addressPairDifference first second third fourth) ratio)
    (hnegative : ∀ ratio ∈ Ioo lower upper,
      |addressPairDifference first second third fourth ratio| < band →
        deriv (addressPairDifference first second third fourth) ratio < 0)
    (hcompact : HasCompactSupport parameterCutoff)
    (hparameterSupport : tsupport parameterCutoff ⊆ Ioo lower upper)
    (hvalueSupport : tsupport valueCutoff ⊆ Ioo (-band) band)
    (hlocal : ∀ value ∈ addressPairDifference first second third fourth ''
      addressPairBand first second third fourth lower upper band,
      DifferentiableAt ℝ (addressPairInverseDensity first second third fourth lower upper band
        parameterCutoff valueCutoff) value ∧
      |deriv (addressPairInverseDensity first second third fourth lower upper band
        parameterCutoff valueCutoff) value| ≤ constant)
    (hkernel : Integrable kernel volume)
    (hproduct : Integrable (fun point => kernel point *
      addressPairExtendedDensity first second third fourth lower upper band parameterCutoff valueCutoff
        (point / frequency)) volume)
    (hmoment : Integrable (fun point => |point| * |kernel point|) volume)
    (hzero : ∫ point, kernel point = 0) :
    |addressPairAnnulus
      (fun ratio => parameterCutoff ratio *
        valueCutoff (addressPairDifference first second third fourth ratio))
      kernel frequency first second third fourth| ≤
      ((constant : ℝ) / frequency) * ∫ point, |point| * |kernel point| := by
  rw [addressPairAnnulus_cutoff_change_variables first second third fourth parameterCutoff valueCutoff
    kernel frequency hband hdifferentiable hnegative
    (fun ratio houtside => image_eq_zero_of_notMem_tsupport (fun h => houtside (hparameterSupport h)))
    (fun value houtside => image_eq_zero_of_notMem_tsupport (fun h => houtside (hvalueSupport h))),
    integral_scaled_addressPairExtendedDensity first second third fourth lower upper band
      parameterCutoff valueCutoff kernel hfrequency]
  apply integral_zero_mean_kernel_scaled_bound kernel
    (addressPairExtendedDensity first second third fourth lower upper band parameterCutoff valueCutoff)
    hfrequency ?_ hkernel hproduct hmoment hzero
  exact lipschitzWith_addressPairExtendedDensity first second third fourth parameterCutoff valueCutoff
    constant (isOpen_addressPairBand_image first second third fourth hband hdifferentiable hnegative)
    (addressPairExtendedDensity_support first second third fourth parameterCutoff valueCutoff
      hdifferentiable hcompact hparameterSupport hvalueSupport).2 hlocal

end LambdaCantor.AE
