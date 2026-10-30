import LambdaCantor.First.RootsL1Convergence
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction
namespace LambdaCantor.First.Roots

/-- Bounded tests pair continuously with genuine L1 densities. -/
theorem L1_bounded_test_tendsto (sequence : ℕ → Lp ℝ 1 volume)
    (density : Lp ℝ 1 volume) (convergence : Tendsto sequence atTop (𝓝 density))
    (test : ℝ →ᵇ ℝ) :
    Tendsto (fun depth => ∫ point, test point * sequence depth point) atTop
      (𝓝 (∫ point, test point * density point)) := by
  have integrable (function : Lp ℝ 1 volume) : Integrable (function : ℝ → ℝ) volume :=
    memLp_one_iff_integrable.mp (Lp.memLp function)
  have product_integrable (function : Lp ℝ 1 volume) :
      Integrable (fun point => test point * function point) volume :=
    (integrable function).bdd_mul test.continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall test.norm_coe_le_norm)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (g := fun depth => ‖test‖ * ‖sequence depth - density‖)
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  · apply Filter.Eventually.of_forall
    intro depth
    rw [← integral_sub (product_integrable (sequence depth)) (product_integrable density)]
    calc
      _ ≤ ∫ point, ‖test point * sequence depth point - test point * density point‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ point, ‖test‖ * ‖sequence depth point - density point‖ := by
        apply integral_mono
          ((product_integrable (sequence depth)).sub (product_integrable density)).norm
          (((integrable (sequence depth)).sub (integrable density)).norm.const_mul _)
        intro point
        change ‖test point * sequence depth point - test point * density point‖ ≤
          ‖test‖ * ‖sequence depth point - density point‖
        rw [← mul_sub, norm_mul]
        exact mul_le_mul_of_nonneg_right (test.norm_coe_le_norm point) (norm_nonneg _)
      _ = ‖test‖ * ‖sequence depth - density‖ := by
        have norm_identity : (∫ point, ‖sequence depth point - density point‖) =
            ‖sequence depth - density‖ := by
          simpa only [dist_eq_norm] using (L1.dist_eq_integral_dist (sequence depth) density).symm
        rw [integral_const_mul, norm_identity]
  · simpa using (tendsto_iff_norm_sub_tendsto_zero.mp convergence).const_mul ‖test‖

theorem measureDensityL1_test_integral (measure : Measure ℝ)
    (density_exists : LinearRegularity.HasL2Density measure) (test : ℝ →ᵇ ℝ) :
    (∫ point, test point * measureDensityL1 measure density_exists point) =
      ∫ point, test point ∂measure := by
  have properties := measureDensity_properties measure density_exists
  refine Eq.trans ?_ (congrArg (fun law : Measure ℝ => ∫ point, test point ∂law)
    properties.2.2.2.2).symm
  rw [integral_withDensity_eq_integral_toReal_smul
    properties.2.1.ennreal_ofReal (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [properties.2.2.1.coeFn_toL1] with point equality
  simp only [measureDensityL1] at equality ⊢
  rw [equality, ENNReal.toReal_ofReal (properties.1 point), smul_eq_mul, mul_comm]

/-- L1 limits of the actual nonnegative kernels represent the restricted root
law, by their independently proved weak convergence. -/
theorem rootSobolevGoodSet_actual_density
    {exponent : ℝ} (data : RootFibreData exponent) (orderIndex bound : ℕ) :
    ∃ density : ℝ → ℝ, (∀ point, 0 ≤ density point) ∧ Measurable density ∧ Integrable density volume ∧
      (pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound)).map data.root =
        volume.withDensity (fun point => ENNReal.ofReal (density point)) := by
  obtain ⟨limit, convergence⟩ := rootSobolevGoodSet_actual_L1_convergence data orderIndex bound
  have limit_nonnegative : (0 : Lp ℝ 1 (volume : Measure ℝ)) ≤ limit := by
    have closed_nonnegative : IsClosed (Set.Ici (0 : Lp ℝ 1 (volume : Measure ℝ))) := isClosed_Ici
    apply closed_nonnegative.mem_of_tendsto convergence
    exact Filter.Eventually.of_forall (fun depth =>
      (show (0 : Lp ℝ 1 (volume : Measure ℝ)) ≤ goodSetKernelDensityL1 data orderIndex bound depth from
        measureDensityL1_nonnegative _ _))
  have limit_integrable : Integrable (limit : ℝ → ℝ) volume :=
    memLp_one_iff_integrable.mp (Lp.memLp limit)
  let density : ℝ → ℝ := fun point => max (limit_integrable.aestronglyMeasurable.mk limit point) 0
  have density_measurable : Measurable density :=
    limit_integrable.aestronglyMeasurable.stronglyMeasurable_mk.measurable.max measurable_const
  have density_nonnegative : ∀ point, 0 ≤ density point := fun _ => le_max_right _ _
  have density_eq : density =ᵐ[volume] (limit : ℝ → ℝ) := by
    filter_upwards [limit_integrable.aestronglyMeasurable.ae_eq_mk,
      (Lp.coeFn_nonneg limit).mpr limit_nonnegative] with point equality nonnegative
    change (0 : ℝ) ≤ (limit : ℝ → ℝ) point at nonnegative
    simp only [density, ← equality, max_eq_left nonnegative]
  have density_integrable : Integrable density volume := limit_integrable.congr density_eq.symm
  let limitMeasure := volume.withDensity (fun point => ENNReal.ofReal (density point))
  have finite_limit : IsFiniteMeasure limitMeasure := by
    constructor
    rw [show limitMeasure = volume.withDensity (fun point => ENNReal.ofReal (density point)) from rfl,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal density_integrable
        (Filter.Eventually.of_forall density_nonnegative)]
    exact ENNReal.ofReal_lt_top
  let actual := (pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound)).map data.root
  have finite_actual : IsFiniteMeasure actual := by dsimp [actual]; infer_instance
  have equality : (⟨actual, finite_actual⟩ : FiniteMeasure ℝ) = ⟨limitMeasure, finite_limit⟩ := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro test
    have strong_limit := L1_bounded_test_tendsto _ limit convergence test
    have weak_limit := prefixNeighborhood_kernel_integral_tendsto data
      (rootSobolevGoodSet data orderIndex bound)
      (rootFibreData_compact_good_set data orderIndex bound).isClosed test test.continuous
      ‖test‖ test.norm_coe_le_norm
    have weak_rewritten : Tendsto (fun depth => ∫ point, test point *
        goodSetKernelDensityL1 data orderIndex bound depth point) atTop
        (𝓝 (∫ point, test point ∂actual)) := by
      convert weak_limit using 1
      · funext depth
        rw [goodSetKernelDensityL1, measureDensityL1_test_integral]
        unfold goodSetKernelLaw
        rw [integral_map (continuous_selectedRootKernel data _ depth).measurable.aemeasurable
          test.continuous.measurable.aestronglyMeasurable, integral_indicator
          (measurableSet_prefixNeighborhood _ depth)]
      · rw [integral_map (rootFibreData_continuous_root data).measurable.aemeasurable
          test.continuous.measurable.aestronglyMeasurable, integral_indicator
          (rootFibreData_compact_good_set data orderIndex bound).measurableSet]
    have identification := tendsto_nhds_unique weak_rewritten strong_limit
    change (∫ point, test point ∂actual) = ∫ point, test point ∂limitMeasure
    rw [identification]
    unfold limitMeasure
    rw [integral_withDensity_eq_integral_toReal_smul density_measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    filter_upwards [density_eq] with point equality
    rw [ENNReal.toReal_ofReal (density_nonnegative point), smul_eq_mul, equality, mul_comm]
  exact ⟨density, density_nonnegative, density_measurable, density_integrable,
    congrArg (fun measure : FiniteMeasure ℝ => (measure : Measure ℝ)) equality⟩

theorem rootSobolevGoodSet_root_law_absolutelyContinuous
    {exponent : ℝ} (data : RootFibreData exponent) (orderIndex bound : ℕ) :
    (pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound)).map data.root ≪ volume := by
  obtain ⟨density, _, _, _, law⟩ := rootSobolevGoodSet_actual_density data orderIndex bound
  rw [law]
  exact withDensity_absolutelyContinuous _ _

end LambdaCantor.First.Roots
