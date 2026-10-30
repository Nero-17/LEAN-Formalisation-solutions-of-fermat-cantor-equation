import LambdaCantor.AE.ConvolutionMeasureCore
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory

namespace LambdaCantor.AE

/-- The actual law of the sum of two independently sampled scaled addresses. -/
def scaledConvolutionProbability (ratio firstScale secondScale : ℝ) : Measure ℝ :=
  (addressProbability.prod addressProbability).map
    (fun digits : (ℕ → Bool) × (ℕ → Bool) =>
      firstScale * address ratio digits.1 + secondScale * address ratio digits.2)

theorem measurable_scaled_sum_addresses (ratio firstScale secondScale : ℝ) :
    Measurable (fun digits : (ℕ → Bool) × (ℕ → Bool) =>
      firstScale * address ratio digits.1 + secondScale * address ratio digits.2) :=
  (((measurable_address_digits ratio).comp measurable_fst).const_mul firstScale).add
    (((measurable_address_digits ratio).comp measurable_snd).const_mul secondScale)

instance (ratio firstScale secondScale : ℝ) :
    IsProbabilityMeasure (scaledConvolutionProbability ratio firstScale secondScale) :=
  Measure.isProbabilityMeasure_map
    (measurable_scaled_sum_addresses ratio firstScale secondScale).aemeasurable

theorem measureFourier_scaledConvolutionProbability
    (ratio firstScale secondScale frequency : ℝ) :
    measureFourier (scaledConvolutionProbability ratio firstScale secondScale) frequency =
      addressFourier ratio (firstScale * frequency) *
        addressFourier ratio (secondScale * frequency) := by
  unfold measureFourier scaledConvolutionProbability
  rw [integral_map (measurable_scaled_sum_addresses ratio firstScale secondScale).aemeasurable
    (measurable_fourier_character frequency).aestronglyMeasurable]
  calc
    _ = ∫ digits : (ℕ → Bool) × (ℕ → Bool),
        (Real.fourierChar (-((firstScale*frequency)*address ratio digits.1)) : ℂ)*
          (Real.fourierChar (-((secondScale*frequency)*address ratio digits.2)) : ℂ)
        ∂addressProbability.prod addressProbability := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun digits => by
        simp only [Real.fourierChar_apply]
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring)
    _ = (∫ digits, (Real.fourierChar (-((firstScale*frequency)*address ratio digits)) : ℂ) ∂addressProbability)*
        (∫ digits, (Real.fourierChar (-((secondScale*frequency)*address ratio digits)) : ℂ) ∂addressProbability) := by
      convert! (integral_prod_mul (μ := addressProbability) (ν := addressProbability)
        (fun digits : ℕ → Bool => (Real.fourierChar (-((firstScale*frequency)*address ratio digits)) : ℂ))
        (fun digits : ℕ → Bool => (Real.fourierChar (-((secondScale*frequency)*address ratio digits)) : ℂ))) using 1
    _ = _ := rfl

/-- A pointwise arithmetic mean estimate is sufficient for the common
Sobolev bound; both terms are actual scaled self-convolution Fourier energies. -/
theorem weighted_scaledConvolution_fourier_bound
    (ratio firstScale secondScale regularity frequency : ℝ) :
    (1 + |frequency| ^ (2 * regularity)) *
      ‖measureFourier (scaledConvolutionProbability ratio firstScale secondScale) frequency‖ ^ 2 ≤
    (1 + |frequency| ^ (2 * regularity)) *
      (‖addressFourier ratio (firstScale * frequency)‖ ^ 4 +
        ‖addressFourier ratio (secondScale * frequency)‖ ^ 4) / 2 := by
  rw [measureFourier_scaledConvolutionProbability, norm_mul]
  have harithmetic :
      (‖addressFourier ratio (firstScale * frequency)‖ *
        ‖addressFourier ratio (secondScale * frequency)‖) ^ 2 ≤
      (‖addressFourier ratio (firstScale * frequency)‖ ^ 4 +
        ‖addressFourier ratio (secondScale * frequency)‖ ^ 4) / 2 := by
    apply sub_nonneg.mp
    rw [show (‖addressFourier ratio (firstScale * frequency)‖ ^ 4 +
        ‖addressFourier ratio (secondScale * frequency)‖ ^ 4) / 2 -
        (‖addressFourier ratio (firstScale * frequency)‖ *
          ‖addressFourier ratio (secondScale * frequency)‖) ^ 2 =
        (‖addressFourier ratio (firstScale * frequency)‖ ^ 2 -
          ‖addressFourier ratio (secondScale * frequency)‖ ^ 2)^2/2 by ring]
    positivity
  have hweight : 0 ≤ 1 + |frequency| ^ (2 * regularity) := by positivity
  calc
    _ ≤ (1 + |frequency| ^ (2 * regularity)) *
        ((‖addressFourier ratio (firstScale * frequency)‖ ^ 4 +
          ‖addressFourier ratio (secondScale * frequency)‖ ^ 4) / 2) :=
      mul_le_mul_of_nonneg_left harithmetic hweight
    _ = _ := by ring

end LambdaCantor.AE
