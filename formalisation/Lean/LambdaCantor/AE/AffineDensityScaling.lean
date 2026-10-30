import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FieldSimp

noncomputable section
open MeasureTheory

namespace LambdaCantor.AE

def physicalAffineDensity (origin width : ℝ) (density : ℝ → ℝ) : ℝ → ℝ :=
  fun value => width⁻¹*density ((value-origin)/width)

theorem integral_affine_inverse (function : ℝ → ℝ) (origin : ℝ)
    {width : ℝ} (width_positive : 0 < width) :
    (∫ value : ℝ, function ((value-origin)/width)) = width*∫ value : ℝ, function value := by
  simp only [div_eq_mul_inv]
  rw [integral_sub_right_eq_self (fun value => function (value*width⁻¹)) origin,
    Measure.integral_comp_mul_right]
  simp only [inv_inv, abs_of_pos width_positive, smul_eq_mul]

theorem integrable_physicalAffineDensity {density : ℝ → ℝ}
    (integrable : Integrable density) (origin : ℝ) {width : ℝ} (width_positive : 0 < width) :
    Integrable (physicalAffineDensity origin width density) := by
  have scaled := (integrable.comp_mul_right' (inv_ne_zero width_positive.ne')).comp_sub_right origin
  change Integrable (fun value : ℝ => width⁻¹*density ((value-origin)/width))
  simpa only [div_eq_mul_inv] using scaled.const_mul width⁻¹

/-- A shared affine normalization preserves the L1 distance exactly. -/
theorem physicalAffineDensity_L1_distance (first second : ℝ → ℝ)
    (origin : ℝ) {width : ℝ} (width_positive : 0 < width) :
    (∫ value : ℝ, |physicalAffineDensity origin width first value-
      physicalAffineDensity origin width second value|) =
        ∫ value : ℝ, |first value-second value| := by
  simp only [physicalAffineDensity, ← mul_sub, abs_mul,
    abs_of_pos (inv_pos.mpr width_positive)]
  rw [integral_const_mul, integral_affine_inverse (fun value => |first value-second value|) origin width_positive]
  field_simp [width_positive.ne']

/-- Physical squared L2 costs one inverse width, as required for the initial
kernel estimate in the density-contradiction argument. -/
theorem physicalAffineDensity_L2_square (density : ℝ → ℝ)
    (origin : ℝ) {width : ℝ} (width_positive : 0 < width) :
    (∫ value : ℝ, |physicalAffineDensity origin width density value|^2) =
      width⁻¹*∫ value : ℝ, |density value|^2 := by
  simp only [physicalAffineDensity, abs_mul, mul_pow, abs_of_pos (inv_pos.mpr width_positive)]
  rw [integral_const_mul, integral_affine_inverse (fun value => |density value|^2) origin width_positive]
  field_simp [width_positive.ne']

end LambdaCantor.AE
