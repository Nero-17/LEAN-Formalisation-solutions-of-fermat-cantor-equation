import LambdaCantor.AE.ScaledFourierEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace LambdaCantor.AE

def scaledConvolutionEnergy (ratio firstScale secondScale regularity : ℝ) : ℝ≥0∞ :=
  ∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) *
    ‖measureFourier (scaledConvolutionProbability ratio firstScale secondScale) frequency‖ ^ 2)

/-- One constant controls the actual Fourier energy for every pair of scales
bounded below by the same positive number. This includes the compact slope
families in the manuscript's common Sobolev bound. -/
theorem common_scaledConvolution_energy_bound
    (ratio : ℝ) {minimumScale firstScale secondScale regularity : ℝ}
    (hminimum : 0 < minimumScale) (hfirst : minimumScale ≤ firstScale)
    (hsecond : minimumScale ≤ secondScale) (hregularity : 0 ≤ regularity) :
    scaledConvolutionEnergy ratio firstScale secondScale regularity ≤
      2 * (ENNReal.ofReal (1 + (minimumScale ^ (2 * regularity))⁻¹) *
        ENNReal.ofReal minimumScale⁻¹ * fullFourierEnergy ratio regularity) := by
  have hweight_measurable : Measurable (fun frequency : ℝ => 1 + |frequency| ^ (2 * regularity)) :=
    (continuous_const.add ((Real.continuous_rpow_const
      (by positivity : 0 ≤ 2 * regularity)).comp continuous_abs)).measurable
  have hmeasurable (scale : ℝ) : Measurable (fun frequency : ℝ =>
      ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) *
        ‖addressFourier ratio (scale * frequency)‖ ^ 4)) :=
    (hweight_measurable.mul
      (((measurable_addressFourier ratio).comp (measurable_id.const_mul scale)).norm.pow_const 4)).ennreal_ofReal
  calc
    _ ≤ ∫⁻ frequency : ℝ,
        ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) *
          ‖addressFourier ratio (firstScale * frequency)‖ ^ 4) +
        ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) *
          ‖addressFourier ratio (secondScale * frequency)‖ ^ 4) := by
      apply lintegral_mono
      intro frequency
      change ENNReal.ofReal _ ≤ ENNReal.ofReal _ + ENNReal.ofReal _
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hpointwise := weighted_scaledConvolution_fourier_bound
        ratio firstScale secondScale regularity frequency
      have hweight : 0 ≤ 1 + |frequency| ^ (2 * regularity) := by positivity
      have hsum : 0 ≤ (1 + |frequency| ^ (2 * regularity)) *
          (‖addressFourier ratio (firstScale * frequency)‖ ^ 4 +
            ‖addressFourier ratio (secondScale * frequency)‖ ^ 4) := by positivity
      nlinarith
    _ = (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) *
          ‖addressFourier ratio (firstScale * frequency)‖ ^ 4)) +
        ∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) *
          ‖addressFourier ratio (secondScale * frequency)‖ ^ 4) :=
      lintegral_add_left (hmeasurable firstScale) _
    _ ≤ _ := by
      simpa only [two_mul] using
        add_le_add (scaled_fourth_energy_bound ratio hminimum hfirst hregularity)
          (scaled_fourth_energy_bound ratio hminimum hsecond hregularity)

theorem scaledConvolutionEnergy_lt_top_of_fullEnergy
    {ratio minimumScale firstScale secondScale regularity : ℝ}
    (hminimum : 0 < minimumScale) (hfirst : minimumScale ≤ firstScale)
    (hsecond : minimumScale ≤ secondScale) (hregularity : 0 ≤ regularity)
    (henergy : fullFourierEnergy ratio regularity < ⊤) :
    scaledConvolutionEnergy ratio firstScale secondScale regularity < ⊤ := by
  apply lt_of_le_of_lt (common_scaledConvolution_energy_bound ratio hminimum hfirst hsecond hregularity)
  exact ENNReal.mul_lt_top (by norm_num)
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) henergy)

end LambdaCantor.AE
