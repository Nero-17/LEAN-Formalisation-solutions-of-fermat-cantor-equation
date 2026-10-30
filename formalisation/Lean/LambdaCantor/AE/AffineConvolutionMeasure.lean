import LambdaCantor.AE.ScaledConvolutionMeasure

noncomputable section
open MeasureTheory

namespace LambdaCantor.AE

/-- Complete affine tail law, including the Newton constant. -/
def affineConvolutionProbability (ratio shift firstScale secondScale : ℝ) : Measure ℝ :=
  (scaledConvolutionProbability ratio firstScale secondScale).map (fun value => shift + value)

instance (ratio shift firstScale secondScale : ℝ) :
    IsProbabilityMeasure (affineConvolutionProbability ratio shift firstScale secondScale) :=
  Measure.isProbabilityMeasure_map (measurable_const.add measurable_id).aemeasurable

theorem measureFourier_affineConvolutionProbability
    (ratio shift firstScale secondScale frequency : ℝ) :
    measureFourier (affineConvolutionProbability ratio shift firstScale secondScale) frequency =
      (Real.fourierChar (-(frequency * shift)) : ℂ) *
        measureFourier (scaledConvolutionProbability ratio firstScale secondScale) frequency := by
  have translation : Measurable (fun value : ℝ => shift+value) := by fun_prop
  unfold affineConvolutionProbability measureFourier
  rw [integral_map translation.aemeasurable
    (measurable_fourier_character frequency).aestronglyMeasurable]
  calc
    _ = ∫ value : ℝ, (Real.fourierChar (-(frequency*shift)) : ℂ)*
        (Real.fourierChar (-(frequency*value)) : ℂ) ∂scaledConvolutionProbability ratio firstScale secondScale := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun value => by
        simp only [Real.fourierChar_apply]
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring)
    _ = _ := by
      convert! (integral_const_mul (μ := scaledConvolutionProbability ratio firstScale secondScale)
        (Real.fourierChar (-(frequency*shift)) : ℂ)
        (fun value : ℝ => (Real.fourierChar (-(frequency*value)) : ℂ))) using 1

theorem norm_measureFourier_affineConvolutionProbability
    (ratio shift firstScale secondScale frequency : ℝ) :
    ‖measureFourier (affineConvolutionProbability ratio shift firstScale secondScale) frequency‖ =
      ‖measureFourier (scaledConvolutionProbability ratio firstScale secondScale) frequency‖ := by
  rw [measureFourier_affineConvolutionProbability, norm_mul]
  simp

/-- The measure is exactly the law of the displayed complete Newton kernel,
not a centered kernel with its constant term omitted. -/
theorem affineConvolutionProbability_eq_address_map
    (ratio shift firstScale secondScale : ℝ) :
    affineConvolutionProbability ratio shift firstScale secondScale =
      (addressProbability.prod addressProbability).map
        (fun digits : (ℕ → Bool) × (ℕ → Bool) =>
          shift + (firstScale * address ratio digits.1 + secondScale * address ratio digits.2)) := by
  have translation : Measurable (fun value : ℝ => shift+value) := by fun_prop
  unfold affineConvolutionProbability scaledConvolutionProbability
  rw [Measure.map_map translation
    (measurable_scaled_sum_addresses ratio firstScale secondScale)]
  rfl

end LambdaCantor.AE
