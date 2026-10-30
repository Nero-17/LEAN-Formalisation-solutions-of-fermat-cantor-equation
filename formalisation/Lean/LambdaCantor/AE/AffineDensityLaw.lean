import LambdaCantor.AE.AffineDensityScaling
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace LambdaCantor.AE

theorem integral_real_withDensity (density function : ℝ → ℝ)
    (measurable : AEStronglyMeasurable density volume) (nonnegative : ∀ value, 0 ≤ density value) :
    (∫ value : ℝ, function value ∂volume.withDensity (fun value => ENNReal.ofReal (density value))) =
      ∫ value : ℝ, density value*function value := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ measurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun value => by
    change (ENNReal.ofReal (density value)).toReal • function value = density value * function value
    rw [ENNReal.toReal_ofReal (nonnegative value), smul_eq_mul])

/-- Affine normalization has the actual pushforward density, with its full
translation and one inverse width. This measure identity connects the
normalized transport densities to the physical Newton mixture laws. -/
theorem map_affine_withDensity (density : ℝ → ℝ)
    (integrable : Integrable density) (nonnegative : ∀ value, 0 ≤ density value)
    (origin : ℝ) {width : ℝ} (width_positive : 0 < width) :
    (volume.withDensity (fun value => ENNReal.ofReal (density value))).map
      (fun value => origin+width*value) =
        volume.withDensity (fun value => ENNReal.ofReal (physicalAffineDensity origin width density value)) := by
  have physical_integrable := integrable_physicalAffineDensity integrable origin width_positive
  have physical_nonnegative : ∀ value, 0 ≤ physicalAffineDensity origin width density value := by
    intro value
    exact mul_nonneg (inv_nonneg.mpr width_positive.le) (nonnegative _)
  have density_finite : (∫⁻ value : ℝ, ENNReal.ofReal (density value)) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal integrable (Eventually.of_forall nonnegative)]
    exact ENNReal.ofReal_ne_top
  have physical_finite : (∫⁻ value : ℝ,
      ENNReal.ofReal (physicalAffineDensity origin width density value)) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal physical_integrable (Eventually.of_forall physical_nonnegative)]
    exact ENNReal.ofReal_ne_top
  letI := isFiniteMeasure_withDensity density_finite
  letI := isFiniteMeasure_withDensity physical_finite
  letI : IsFiniteMeasure ((volume.withDensity (fun value => ENNReal.ofReal (density value))).map
      (fun value => origin+width*value)) :=
    (volume.withDensity (fun value => ENNReal.ofReal (density value))).isFiniteMeasure_map _
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro test
  rw [integral_map (show Measurable (fun value : ℝ => origin + width * value) from
    measurable_const.add (measurable_const.mul measurable_id)).aemeasurable
    test.continuous.measurable.aestronglyMeasurable,
    integral_real_withDensity density (fun value => test (origin+width*value)) integrable.aestronglyMeasurable nonnegative,
    integral_real_withDensity (physicalAffineDensity origin width density) test physical_integrable.aestronglyMeasurable physical_nonnegative]
  symm
  calc
    _ = width⁻¹*∫ value : ℝ,
        density ((value-origin)/width)*test (origin+width*((value-origin)/width)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun value => by
        have identity : origin+width*((value-origin)/width) = value := by
          field_simp [width_positive.ne']
          <;> ring
        change physicalAffineDensity origin width density value * test value =
          width⁻¹ * (density ((value-origin)/width) * test (origin+width*((value-origin)/width)))
        rw [identity]
        unfold physicalAffineDensity
        ring)
    _ = width⁻¹*(width*∫ value : ℝ, density value*test (origin+width*value)) := by
      rw [integral_affine_inverse (fun value => density value*test (origin+width*value)) origin width_positive]
    _ = _ := by
      field_simp [width_positive.ne']

end LambdaCantor.AE
