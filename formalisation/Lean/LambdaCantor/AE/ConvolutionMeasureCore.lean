import LambdaCantor.AE.AddressProbability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section
open MeasureTheory

namespace LambdaCantor.AE

def cantorProbability (ratio : ℝ) : Measure ℝ := addressProbability.map (address ratio)

instance (ratio : ℝ) : IsProbabilityMeasure (cantorProbability ratio) :=
  Measure.isProbabilityMeasure_map (measurable_address_digits ratio).aemeasurable

def selfConvolutionProbability (ratio : ℝ) : Measure ℝ :=
  (addressProbability.prod addressProbability).map
    (fun digits : (ℕ → Bool) × (ℕ → Bool) => address ratio digits.1 + address ratio digits.2)

theorem measurable_sum_addresses (ratio : ℝ) :
    Measurable (fun digits : (ℕ → Bool) × (ℕ → Bool) =>
      address ratio digits.1 + address ratio digits.2) :=
  ((measurable_address_digits ratio).comp measurable_fst).add
    ((measurable_address_digits ratio).comp measurable_snd)

instance (ratio : ℝ) : IsProbabilityMeasure (selfConvolutionProbability ratio) :=
  Measure.isProbabilityMeasure_map (measurable_sum_addresses ratio).aemeasurable

def measureFourier (probability : Measure ℝ) (frequency : ℝ) : ℂ :=
  ∫ value, (Real.fourierChar (-(frequency * value)) : ℂ) ∂probability

theorem measurable_fourier_character (frequency : ℝ) :
    Measurable (fun value : ℝ => (Real.fourierChar (-(frequency * value)) : ℂ)) := by
  have character_continuous : Continuous (fun value : ℝ => (Real.fourierChar value : ℂ)) := by
    simp only [Real.fourierChar_apply]
    fun_prop
  exact character_continuous.measurable.comp (measurable_const.mul measurable_id).neg

theorem measureFourier_cantorProbability (ratio frequency : ℝ) :
    measureFourier (cantorProbability ratio) frequency = addressFourier ratio frequency := by
  unfold measureFourier cantorProbability addressFourier
  rw [integral_map (measurable_address_digits ratio).aemeasurable
    (measurable_fourier_character frequency).aestronglyMeasurable]

theorem measureFourier_selfConvolutionProbability (ratio frequency : ℝ) :
    measureFourier (selfConvolutionProbability ratio) frequency = (addressFourier ratio frequency)^2 := by
  unfold measureFourier selfConvolutionProbability
  rw [integral_map (measurable_sum_addresses ratio).aemeasurable
    (measurable_fourier_character frequency).aestronglyMeasurable]
  calc
    _ = ∫ digits : (ℕ → Bool) × (ℕ → Bool),
        (Real.fourierChar (-(frequency*address ratio digits.1)) : ℂ)*
          (Real.fourierChar (-(frequency*address ratio digits.2)) : ℂ)
        ∂addressProbability.prod addressProbability := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun digits => by
        simp only [Real.fourierChar_apply]
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring)
    _ = (∫ digits, (Real.fourierChar (-(frequency*address ratio digits)) : ℂ) ∂addressProbability)*
        (∫ digits, (Real.fourierChar (-(frequency*address ratio digits)) : ℂ) ∂addressProbability) := by
      convert! (integral_prod_mul (μ := addressProbability) (ν := addressProbability)
        (fun digits : ℕ → Bool => (Real.fourierChar (-(frequency*address ratio digits)) : ℂ))
        (fun digits : ℕ → Bool => (Real.fourierChar (-(frequency*address ratio digits)) : ℂ))) using 1
    _ = _ := by rw [pow_two]; rfl

theorem norm_measureFourier_selfConvolution_sq (ratio frequency : ℝ) :
    ‖measureFourier (selfConvolutionProbability ratio) frequency‖^2 =
      ‖addressFourier ratio frequency‖^4 := by
  rw [measureFourier_selfConvolutionProbability, norm_pow, ← pow_mul]

end LambdaCantor.AE
