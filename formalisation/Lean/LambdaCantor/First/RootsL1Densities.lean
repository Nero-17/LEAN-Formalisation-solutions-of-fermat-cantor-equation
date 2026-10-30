import LambdaCantor.First.RootsKernelSumDensity
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.LpOrder

noncomputable section
open MeasureTheory
namespace LambdaCantor.First.Roots

def measureDensity (measure : Measure ℝ) (density_exists : LinearRegularity.HasL2Density measure) : ℝ → ℝ :=
  Classical.choose density_exists

theorem measureDensity_properties (measure : Measure ℝ) (density_exists : LinearRegularity.HasL2Density measure) :
    (∀ point, 0 ≤ measureDensity measure density_exists point) ∧ Measurable (measureDensity measure density_exists) ∧
      Integrable (measureDensity measure density_exists) volume ∧ MemLp (measureDensity measure density_exists) 2 volume ∧
      measure = volume.withDensity (fun point => ENNReal.ofReal (measureDensity measure density_exists point)) :=
  Classical.choose_spec density_exists

def measureDensityL1 (measure : Measure ℝ) (density_exists : LinearRegularity.HasL2Density measure) : Lp ℝ 1 (volume : Measure ℝ) :=
  (measureDensity_properties measure density_exists).2.2.1.toL1 (measureDensity measure density_exists)

theorem nonnegative_density_unique {measure : Measure ℝ} (first second : ℝ → ℝ)
    (first_nonnegative : ∀ point, 0 ≤ first point) (second_nonnegative : ∀ point, 0 ≤ second point)
    (first_measurable : Measurable first) (second_measurable : Measurable second)
    (first_law : measure = volume.withDensity (fun point => ENNReal.ofReal (first point)))
    (second_law : measure = volume.withDensity (fun point => ENNReal.ofReal (second point))) :
    first =ᵐ[volume] second := by
  have equality := (withDensity_eq_iff_of_sigmaFinite first_measurable.ennreal_ofReal.aemeasurable
    second_measurable.ennreal_ofReal.aemeasurable).mp (first_law.symm.trans second_law)
  filter_upwards [equality] with point equality
  exact (ENNReal.ofReal_eq_ofReal_iff (first_nonnegative point) (second_nonnegative point)).mp equality

/-- Passing to L1 removes all choices of pointwise density representatives. -/
theorem measureDensityL1_eq_toL1 (measure : Measure ℝ) (density_exists : LinearRegularity.HasL2Density measure)
    (density : ℝ → ℝ) (nonnegative : ∀ point, 0 ≤ density point) (measurable : Measurable density)
    (integrable : Integrable density volume)
    (law : measure = volume.withDensity (fun point => ENNReal.ofReal (density point))) :
    measureDensityL1 measure density_exists = integrable.toL1 density := by
  apply (Integrable.toL1_eq_toL1_iff _ _ _ _).2
  exact nonnegative_density_unique _ _ (measureDensity_properties measure density_exists).1 nonnegative
    (measureDensity_properties measure density_exists).2.1 measurable
    (measureDensity_properties measure density_exists).2.2.2.2 law

theorem measureDensityL1_nonnegative (measure : Measure ℝ) (density_exists : LinearRegularity.HasL2Density measure) :
    0 ≤ measureDensityL1 measure density_exists := by
  unfold measureDensityL1
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [(measureDensity_properties measure density_exists).2.2.1.coeFn_toL1] with point equality
  change (0 : ℝ) ≤ ((measureDensity_properties measure density_exists).2.2.1.toL1
    (measureDensity measure density_exists)) point
  rw [equality]
  exact (measureDensity_properties measure density_exists).1 point

theorem measureDensityL1_norm (measure : Measure ℝ) (density_exists : LinearRegularity.HasL2Density measure) :
    ‖measureDensityL1 measure density_exists‖ = measure.real Set.univ := by
  have mass := congrArg (fun law : Measure ℝ => law.real Set.univ)
    (measureDensity_properties measure density_exists).2.2.2.2
  simp only [measureReal_def] at mass
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (measureDensity_properties measure density_exists).2.2.1
      (Filter.Eventually.of_forall (measureDensity_properties measure density_exists).1),
    ENNReal.toReal_ofReal (integral_nonneg (measureDensity_properties measure density_exists).1)] at mass
  unfold measureDensityL1
  rw [L1.norm_of_fun_eq_integral_norm]
  simp_rw [Real.norm_eq_abs, abs_of_nonneg ((measureDensity_properties measure density_exists).1 _)]
  exact mass.symm
theorem measureDensityL1_distance {firstMeasure secondMeasure : Measure ℝ}
    (first_exists : LinearRegularity.HasL2Density firstMeasure) (second_exists : LinearRegularity.HasL2Density secondMeasure)
    (first second : ℝ → ℝ) (first_nonnegative : ∀ point, 0 ≤ first point) (second_nonnegative : ∀ point, 0 ≤ second point)
    (first_measurable : Measurable first) (second_measurable : Measurable second)
    (first_integrable : Integrable first volume) (second_integrable : Integrable second volume)
    (first_law : firstMeasure = volume.withDensity (fun point => ENNReal.ofReal (first point)))
    (second_law : secondMeasure = volume.withDensity (fun point => ENNReal.ofReal (second point))) :
    ‖measureDensityL1 firstMeasure first_exists - measureDensityL1 secondMeasure second_exists‖ =
      ∫ point : ℝ, |first point - second point| := by
  rw [measureDensityL1_eq_toL1 _ first_exists first first_nonnegative first_measurable first_integrable first_law,
    measureDensityL1_eq_toL1 _ second_exists second second_nonnegative second_measurable second_integrable second_law,
    ← Integrable.toL1_sub, L1.norm_of_fun_eq_integral_norm]
  simp only [Pi.sub_apply, Real.norm_eq_abs]

end LambdaCantor.First.Roots


