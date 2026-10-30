import LambdaCantor.AE.ExternalPlancherelDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open MeasureTheory Filter
open scoped FourierTransform ENNReal

namespace LambdaCantor.AE

theorem classical_measurable_measureFourier (measure : Measure ℝ) [IsFiniteMeasure measure] :
    Measurable (measureFourier measure) := by
  have character_continuous : Continuous (fun value : ℝ => (Real.fourierChar value : ℂ)) := by
    simp only [Real.fourierChar_apply]
    fun_prop
  have measurable : Measurable (fun pair : ℝ × ℝ =>
      (Real.fourierChar (-(pair.1*pair.2)) : ℂ)) :=
    character_continuous.measurable.comp (measurable_fst.mul measurable_snd).neg
  have integral : StronglyMeasurable (fun frequency : ℝ =>
      ∫ point : ℝ, (Real.fourierChar (-(frequency*point)) : ℂ) ∂measure) :=
    measurable.stronglyMeasurable.integral_prod_right'
  exact integral.measurable

theorem classical_fourier_memLp_of_weighted_energy
    (measure : Measure ℝ) [IsFiniteMeasure measure] {regularity : ℝ}
    (energy_finite : (∫⁻ frequency : ℝ, ENNReal.ofReal
      ((1+|frequency|^(2*regularity))*‖measureFourier measure frequency‖^2)) < ⊤) :
    MemLp (measureFourier measure) 2 volume := by
  have measurable := classical_measurable_measureFourier measure
  apply (memLp_two_iff_integrable_sq_norm measurable.aestronglyMeasurable).mpr
  refine ⟨(measurable.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))]
  apply lt_of_le_of_lt _ energy_finite
  apply lintegral_mono
  intro frequency
  apply ENNReal.ofReal_le_ofReal
  have weight_nonnegative := Real.rpow_nonneg (abs_nonneg frequency) (2*regularity)
  nlinarith [sq_nonneg ‖measureFourier measure frequency‖]

theorem classical_fourier_density_eq_measureFourier {density : ℝ → ℝ}
    (measurable : AEStronglyMeasurable density volume)
    (nonnegative : ∀ᵐ point : ℝ, 0 ≤ density point) (frequency : ℝ) :
    𝓕 (fun point => (density point : ℂ)) frequency =
      measureFourier (volume.withDensity (fun point => ENNReal.ofReal (density point))) frequency := by
  rw [measureFourier, integral_withDensity_eq_integral_toReal_smul₀
    measurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)), Real.fourier_real_eq]
  apply integral_congr_ae
  filter_upwards [nonnegative] with point point_nonnegative
  rw [ENNReal.toReal_ofReal point_nonnegative]
  simp only [Circle.smul_def, smul_eq_mul, Complex.real_smul]
  rw [mul_comm point frequency, mul_comm]

end LambdaCantor.AE
