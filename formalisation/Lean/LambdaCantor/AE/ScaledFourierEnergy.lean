import LambdaCantor.AE.ScaledConvolutionMeasure
import LambdaCantor.AE.FourierEnergyDefinition
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace LambdaCantor.AE

theorem lintegral_comp_positive_mul (function : ℝ → ℝ≥0∞) {scale : ℝ}
    (hscale : 0 < scale) :
    (∫⁻ value : ℝ, function (scale * value)) =
      ENNReal.ofReal scale⁻¹ * ∫⁻ value : ℝ, function value := by
  have hmap := lintegral_map_equiv (μ := volume) function
    (Homeomorph.smul (Units.mk0 scale hscale.ne')).toMeasurableEquiv
  change (∫⁻ value, function value ∂Measure.map (fun value : ℝ => scale • value) volume) =
    ∫⁻ value : ℝ, function (scale * value) at hmap
  rw [← hmap, Measure.map_addHaar_smul volume hscale.ne', lintegral_smul_measure]
  simp only [Module.finrank_self, pow_one, abs_of_pos (inv_pos.mpr hscale), smul_eq_mul]

theorem sobolev_weight_scaled_bound {minimumScale scale regularity : ℝ}
    (hminimum : 0 < minimumScale) (hscale : minimumScale ≤ scale)
    (hregularity : 0 ≤ regularity) (frequency : ℝ) :
    1 + |frequency| ^ (2 * regularity) ≤
      (1 + (minimumScale ^ (2 * regularity))⁻¹) *
        (1 + |scale * frequency| ^ (2 * regularity)) := by
  have hpositive := hminimum.trans_le hscale
  have hpower : 0 < minimumScale ^ (2 * regularity) := Real.rpow_pos_of_pos hminimum _
  have hscaled : minimumScale ^ (2 * regularity) * |frequency| ^ (2 * regularity) ≤
      |scale * frequency| ^ (2 * regularity) := by
    rw [abs_mul, abs_of_pos hpositive, Real.mul_rpow hpositive.le (abs_nonneg frequency)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hminimum.le hscale (by positivity)) (Real.rpow_nonneg (abs_nonneg frequency) _)
  have hbound : |frequency| ^ (2 * regularity) ≤
      (minimumScale ^ (2 * regularity))⁻¹ * |scale * frequency| ^ (2 * regularity) := by
    exact (le_inv_mul_iff₀ hpower).mpr hscaled
  have hnonnegative := Real.rpow_nonneg (abs_nonneg (scale * frequency)) (2 * regularity)
  have hinverse := (inv_pos.mpr hpower).le
  nlinarith

/-- Uniform control for every scale above a fixed positive minimum. In
particular this gives one common bound on any compact interval of slopes. -/
theorem scaled_fourth_energy_bound (ratio : ℝ) {minimumScale scale regularity : ℝ}
    (hminimum : 0 < minimumScale) (hscale : minimumScale ≤ scale)
    (hregularity : 0 ≤ regularity) :
    (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) *
      ‖addressFourier ratio (scale * frequency)‖ ^ 4)) ≤
    ENNReal.ofReal (1 + (minimumScale ^ (2 * regularity))⁻¹) *
      ENNReal.ofReal minimumScale⁻¹ * fullFourierEnergy ratio regularity := by
  have hpositive := hminimum.trans_le hscale
  calc
    _ ≤ ∫⁻ frequency : ℝ,
        ENNReal.ofReal (1 + (minimumScale ^ (2 * regularity))⁻¹) *
          ENNReal.ofReal ((1 + |scale * frequency| ^ (2 * regularity)) *
            ‖addressFourier ratio (scale * frequency)‖ ^ 4) := by
      apply lintegral_mono
      intro frequency
      change ENNReal.ofReal _ ≤ ENNReal.ofReal _ * ENNReal.ofReal _
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ ((1 + (minimumScale ^ (2 * regularity))⁻¹) *
            (1 + |scale * frequency| ^ (2 * regularity))) *
            ‖addressFourier ratio (scale * frequency)‖ ^ 4 :=
          mul_le_mul_of_nonneg_right
            (sobolev_weight_scaled_bound hminimum hscale hregularity frequency)
            (pow_nonneg (norm_nonneg (addressFourier ratio (scale * frequency))) 4)
        _ = _ := mul_assoc _ _ _
    _ = ENNReal.ofReal (1 + (minimumScale ^ (2 * regularity))⁻¹) *
        (ENNReal.ofReal scale⁻¹ * fullFourierEnergy ratio regularity) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      exact lintegral_comp_positive_mul
        (fun value => ENNReal.ofReal ((1 + |value| ^ (2 * regularity)) *
          ‖addressFourier ratio value‖ ^ 4)) hpositive
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_left' (mul_le_mul_right'
        (ENNReal.ofReal_le_ofReal ((inv_le_inv₀ hpositive hminimum).mpr hscale)) _) _

end LambdaCantor.AE
