import LambdaCantor.First.RootsAffineDensity
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

theorem norm_charFun_affine (measure : Measure ℝ) [IsFiniteMeasure measure]
    (center scale frequency : ℝ) :
    ‖charFun (measure.map (fun point : ℝ => center + scale * point)) frequency‖ =
      ‖charFun measure (scale * frequency)‖ := by
  have composition : measure.map (fun point : ℝ => center + scale * point) =
      (measure.map (fun point : ℝ => scale * point)).map (fun point : ℝ => center + point) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [composition, charFun_map_const_add, charFun_map_mul, norm_mul]
  simp [Complex.norm_exp]

theorem affine_frequency_weight (lowerScale scale order frequency : ℝ)
    (lower_positive : 0 < lowerScale) (scale_lower : lowerScale ≤ |scale|)
    (order_nonnegative : 0 ≤ order) :
    (1 + frequency ^ 2) ^ order ≤
      (1 + lowerScale⁻¹ ^ 2) ^ order * (1 + (scale * frequency) ^ 2) ^ order := by
  have square_lower : lowerScale ^ 2 ≤ scale ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ lower_positive.le (abs_nonneg scale)).2 scale_lower
  have inverse_identity : lowerScale⁻¹ ^ 2 * lowerScale ^ 2 = 1 := by
    field_simp [lower_positive.ne']
  have inverse_bound := mul_le_mul_of_nonneg_left square_lower (sq_nonneg lowerScale⁻¹)
  have scaled := mul_le_mul_of_nonneg_right inverse_bound (sq_nonneg frequency)
  rw [inverse_identity] at scaled
  have base_bound : 1 + frequency ^ 2 ≤ (1 + lowerScale⁻¹ ^ 2) * (1 + (scale * frequency) ^ 2) := by
    nlinarith [sq_nonneg lowerScale⁻¹, sq_nonneg (scale * frequency), mul_pow scale frequency 2]
  calc
    _ ≤ ((1 + lowerScale⁻¹ ^ 2) * (1 + (scale * frequency) ^ 2)) ^ order :=
      Real.rpow_le_rpow (by positivity) base_bound order_nonnegative
    _ = _ := Real.mul_rpow (by positivity) (by positivity)

/-- Uniform affine Sobolev energy control uses only a positive lower bound on
the dilation; translations disappear from the characteristic-function norm. -/
theorem affine_characteristic_energy_bound (measure : Measure ℝ) [IsFiniteMeasure measure]
    (center scale lowerScale order : ℝ) (lower_positive : 0 < lowerScale)
    (scale_lower : lowerScale ≤ |scale|) (order_nonnegative : 0 ≤ order) :
    (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ order *
      ‖charFun (measure.map (fun point : ℝ => center + scale * point)) frequency‖ ^ 2)) ≤
      ENNReal.ofReal ((1 + lowerScale⁻¹ ^ 2) ^ order) * ENNReal.ofReal lowerScale⁻¹ *
        (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ order * ‖charFun measure frequency‖ ^ 2)) := by
  have scale_nonzero : scale ≠ 0 := by
    intro zero
    rw [zero, abs_zero] at scale_lower
    linarith
  let energy : ℝ → ℝ≥0∞ := fun frequency =>
    ENNReal.ofReal ((1 + frequency ^ 2) ^ order * ‖charFun measure frequency‖ ^ 2)
  have energy_measurable : Measurable energy := by
    have characteristic_measurable := measurable_charFun (μ := measure)
    unfold energy
    fun_prop
  have substitution : (∫⁻ frequency : ℝ, energy (scale * frequency)) =
      ENNReal.ofReal |scale|⁻¹ * ∫⁻ frequency : ℝ, energy frequency := by
    rw [← lintegral_map energy_measurable (by fun_prop), Real.map_volume_mul_left scale_nonzero,
      lintegral_smul_measure]
    simp only [abs_inv, smul_eq_mul]
  have inverse_bound : |scale|⁻¹ ≤ lowerScale⁻¹ := inv_anti₀ lower_positive scale_lower
  calc
    _ ≤ ∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + lowerScale⁻¹ ^ 2) ^ order) * energy (scale * frequency) := by
      apply lintegral_mono
      intro frequency
      change ENNReal.ofReal ((1 + frequency ^ 2) ^ order *
          ‖charFun (measure.map (fun point : ℝ => center + scale * point)) frequency‖ ^ 2) ≤
        ENNReal.ofReal ((1 + lowerScale⁻¹ ^ 2) ^ order) * energy (scale * frequency)
      rw [norm_charFun_affine]
      dsimp [energy]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
      apply ENNReal.ofReal_le_ofReal
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (affine_frequency_weight lowerScale scale order frequency lower_positive scale_lower order_nonnegative)
        (sq_nonneg _)
    _ = ENNReal.ofReal ((1 + lowerScale⁻¹ ^ 2) ^ order) *
        (ENNReal.ofReal |scale|⁻¹ * ∫⁻ frequency : ℝ, energy frequency) := by
      have scaled_measurable : Measurable (fun frequency : ℝ => energy (scale * frequency)) :=
        energy_measurable.comp (by fun_prop)
      rw [lintegral_const_mul (f := fun frequency : ℝ => energy (scale * frequency)) _ scaled_measurable,
        substitution]
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_left' (mul_le_mul_right' (ENNReal.ofReal_le_ofReal inverse_bound) _) _

end LambdaCantor.First.Roots

