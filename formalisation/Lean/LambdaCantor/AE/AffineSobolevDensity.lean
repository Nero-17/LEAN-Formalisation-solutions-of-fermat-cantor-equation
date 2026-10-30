import LambdaCantor.AE.AffineConvolutionMeasure
import LambdaCantor.AE.ClassicalAffineSobolevDensity

noncomputable section
open MeasureTheory Filter
open scoped ENNReal FourierTransform

namespace LambdaCantor.AE

theorem measurable_affineConvolutionFourier (ratio shift firstScale secondScale : ℝ) :
    Measurable (measureFourier (affineConvolutionProbability ratio shift firstScale secondScale)) := by
  exact classical_measurable_measureFourier _

theorem affineConvolutionFourier_memLp_two {ratio shift firstScale secondScale regularity : ℝ}
    (henergy : scaledConvolutionEnergy ratio firstScale secondScale regularity < ⊤) :
    MemLp (measureFourier (affineConvolutionProbability ratio shift firstScale secondScale)) 2 volume := by
  apply classical_fourier_memLp_of_weighted_energy _
  simpa only [norm_measureFourier_affineConvolutionProbability, scaledConvolutionEnergy] using henergy

/-- A translated affine tail law has an actual density, with the same common
Sobolev energy bound as its scaled convolution. The Newton shift costs nothing. -/
theorem exists_common_affineSobolev_density
    {ratio shift minimumScale firstScale secondScale regularity : ℝ}
    (hminimum : 0 < minimumScale) (hfirst : minimumScale ≤ firstScale)
    (hsecond : minimumScale ≤ secondScale) (hregularity : 0 ≤ regularity)
    (henergy : fullFourierEnergy ratio regularity < ⊤) :
    ∃ density : ℝ → ℝ, Integrable density ∧ MemLp density 2 volume ∧
      (∀ᵐ value : ℝ, 0 ≤ density value) ∧
      affineConvolutionProbability ratio shift firstScale secondScale =
        volume.withDensity (fun value => ENNReal.ofReal (density value)) ∧
      (∫ value : ℝ, |density value| ^ 2) ≤
        ∫ frequency : ℝ,
          ‖measureFourier (scaledConvolutionProbability ratio firstScale secondScale) frequency‖ ^ 2 ∧
      (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) *
        ‖𝓕 (fun value => (density value : ℂ)) frequency‖ ^ 2)) ≤
        2 * (ENNReal.ofReal (1 + (minimumScale ^ (2 * regularity))⁻¹) *
          ENNReal.ofReal minimumScale⁻¹ * fullFourierEnergy ratio regularity) := by
  obtain ⟨density, hintegrable, hLp, hnonnegative, hmeasure, hphysical, hweighted⟩ :=
    classical_exists_common_affineSobolev_density (shift := shift)
      hminimum hfirst hsecond hregularity henergy
  exact ⟨density, hintegrable, hLp, hnonnegative, hmeasure, hphysical.le, hweighted⟩

end LambdaCantor.AE
