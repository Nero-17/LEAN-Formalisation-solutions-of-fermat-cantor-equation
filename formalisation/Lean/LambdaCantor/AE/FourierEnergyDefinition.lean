import LambdaCantor.AE.AddressProbability
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace LambdaCantor.AE

/-- The common self-convolution Fourier energy. Its definition is independent
of any parameter-averaging estimate. -/
def fullFourierEnergy (ratio regularity : ℝ) : ℝ≥0∞ :=
  ∫⁻ frequency : ℝ, ENNReal.ofReal
    ((1+|frequency|^(2*regularity))*‖addressFourier ratio frequency‖^4)

theorem measurable_addressFourier (ratio : ℝ) : Measurable (addressFourier ratio) := by
  have character_continuous : Continuous (fun value : ℝ => (Real.fourierChar value : ℂ)) := by
    simp only [Real.fourierChar_apply]
    fun_prop
  have measurable : Measurable (fun frequencyAndDigits : ℝ × (ℕ → Bool) =>
      (Real.fourierChar (-(frequencyAndDigits.1*address ratio frequencyAndDigits.2)) : ℂ)) :=
    character_continuous.measurable.comp
      (measurable_fst.mul ((measurable_address_digits ratio).comp measurable_snd)).neg
  exact measurable.stronglyMeasurable.integral_prod_right'.measurable

end LambdaCantor.AE
