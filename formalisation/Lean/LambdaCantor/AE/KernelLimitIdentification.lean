import LambdaCantor.AE.KernelMassTransfer
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace LambdaCantor.AE

theorem bounded_test_integral_L1_bound (first second : Lp ℝ 1 volume) (test : ℝ →ᵇ ℝ) :
    |(∫ point : ℝ, first point * test point) -
      ∫ point : ℝ, second point * test point| ≤ ‖test‖ * ‖first - second‖ := by
  have first_integrable := (L1.integrable_coeFn first).mul_bdd
    test.continuous.measurable.aestronglyMeasurable
    (Eventually.of_forall test.norm_coe_le_norm)
  have second_integrable := (L1.integrable_coeFn second).mul_bdd
    test.continuous.measurable.aestronglyMeasurable
    (Eventually.of_forall test.norm_coe_le_norm)
  rw [← integral_sub first_integrable second_integrable]
  calc
    _ ≤ ∫ point : ℝ, |first point * test point - second point * test point| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun point : ℝ => first point * test point - second point * test point)
    _ ≤ ∫ point : ℝ, ‖test‖ * |first point - second point| := by
      apply integral_mono (first_integrable.sub second_integrable).abs
        (((L1.integrable_coeFn first).sub (L1.integrable_coeFn second)).abs.const_mul ‖test‖)
      intro point
      change |first point * test point - second point * test point| ≤
        ‖test‖ * |first point - second point|
      rw [← sub_mul, abs_mul]
      exact (mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using test.norm_coe_le_norm point)
        (abs_nonneg _)).trans_eq (mul_comm _ _)
    _ = ‖test‖ * ‖first - second‖ := by
      rw [integral_const_mul, L1.norm_eq_integral_norm]
      congr 1
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub first second] with point equality
      rw [equality, Pi.sub_apply, Real.norm_eq_abs]

theorem bounded_test_integral_tendsto_of_L1
    (kernels : ℕ → Lp ℝ 1 volume) (density : Lp ℝ 1 volume)
    (convergence : Tendsto kernels atTop (𝓝 density)) (test : ℝ →ᵇ ℝ) :
    Tendsto (fun depth => ∫ point : ℝ, kernels depth point * test point) atTop
      (𝓝 (∫ point : ℝ, density point * test point)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have vanishing : Tendsto (fun depth => ‖test‖ * ‖kernels depth - density‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      (convergence.sub (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => density) atTop (𝓝 density))).norm.const_mul ‖test‖
  apply squeeze_zero
    (fun depth => norm_nonneg _) (fun depth => ?_) vanishing
  simpa only [Real.norm_eq_abs] using bounded_test_integral_L1_bound (kernels depth) density test

/-- Same-address convergence identifies the L1 limit with the true root law.
Only measurable observables and pointwise convergence under the actual source
probability enter; no root-law identification theorem is assumed. -/
theorem l1_limit_eq_root_law_of_same_source
    {Source : Type*} [MeasurableSpace Source]
    (source : Measure Source) [IsFiniteMeasure source]
    (observables : ℕ → Source → ℝ) (root : Source → ℝ)
    (observables_measurable : ∀ depth, Measurable (observables depth))
    (root_measurable : Measurable root)
    (pointwise : ∀ᵐ sample ∂source,
      Tendsto (fun depth => observables depth sample) atTop (𝓝 (root sample)))
    (kernels : ℕ → Lp ℝ 1 volume) (density : Lp ℝ 1 volume)
    (kernels_nonnegative : ∀ depth, 0 ≤ kernels depth)
    (kernel_laws : ∀ depth, source.map (observables depth) =
      volume.withDensity (fun point => ENNReal.ofReal (kernels depth point)))
    (convergence : Tendsto kernels atTop (𝓝 density)) :
    source.map root = volume.withDensity (fun point => ENNReal.ofReal (density point)) := by
  have density_nonnegative : 0 ≤ density :=
    (isClosed_Ici : IsClosed (Set.Ici (0 : Lp ℝ 1 volume))).mem_of_tendsto
      convergence (Eventually.of_forall kernels_nonnegative)
  have density_nonnegative_ae := (Lp.coeFn_nonneg density).mpr density_nonnegative
  have finite_density : (∫⁻ point : ℝ, ENNReal.ofReal (density point)) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal (L1.integrable_coeFn density) density_nonnegative_ae]
    exact ENNReal.ofReal_ne_top
  letI := isFiniteMeasure_withDensity finite_density
  letI : IsFiniteMeasure (source.map root) := source.isFiniteMeasure_map root
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro test
  have source_convergence : Tendsto
      (fun depth => ∫ sample, test (observables depth sample) ∂source) atTop
      (𝓝 (∫ sample, test (root sample) ∂source)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖test‖)
    · intro depth
      exact (test.continuous.measurable.comp (observables_measurable depth)).aestronglyMeasurable
    · exact integrable_const ‖test‖
    · intro depth
      exact Eventually.of_forall (fun sample => test.norm_coe_le_norm _)
    · filter_upwards [pointwise] with sample convergence
      exact test.continuous.continuousAt.tendsto.comp convergence
  have kernel_integral : ∀ depth,
      (∫ sample, test (observables depth sample) ∂source) =
        ∫ point : ℝ, kernels depth point * test point := by
    intro depth
    rw [← integral_map (observables_measurable depth).aemeasurable
      test.continuous.measurable.aestronglyMeasurable, kernel_laws depth,
      integral_withDensity_eq_integral_toReal_smul₀
        (Lp.aestronglyMeasurable (kernels depth)).aemeasurable.ennreal_ofReal
        (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    filter_upwards [(Lp.coeFn_nonneg (kernels depth)).mpr (kernels_nonnegative depth)] with point nonnegative
    rw [ENNReal.toReal_ofReal nonnegative, smul_eq_mul]
  have equality := tendsto_nhds_unique source_convergence
    ((bounded_test_integral_tendsto_of_L1 kernels density convergence test).congr
      (fun depth => (kernel_integral depth).symm))
  rw [integral_map root_measurable.aemeasurable test.continuous.measurable.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀
      (Lp.aestronglyMeasurable density).aemeasurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  refine equality.trans (integral_congr_ae ?_)
  filter_upwards [density_nonnegative_ae] with point nonnegative
  rw [ENNReal.toReal_ofReal nonnegative, smul_eq_mul]

/-- The measure identity gives the exact integral on the good parameter set,
including when that set has infinite ambient Lebesgue measure. -/
theorem setIntegral_eq_real_measure_of_density
    (law : Measure ℝ) (density : Lp ℝ 1 volume)
    (nonnegative : 0 ≤ density)
    (density_law : law = volume.withDensity (fun point => ENNReal.ofReal (density point)))
    (parameters : Set ℝ) (parameters_measurable : MeasurableSet parameters) :
    (∫ point in parameters, density point) = law.real parameters := by
  have nonnegative_ae := (Lp.coeFn_nonneg density).mpr nonnegative
  have restricted_nonnegative := ae_restrict_of_ae (s := parameters) nonnegative_ae
  rw [measureReal_def, density_law, withDensity_apply _ parameters_measurable,
    ← ofReal_integral_eq_lintegral_ofReal
      (L1.integrable_coeFn density).integrableOn restricted_nonnegative,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae restricted_nonnegative)]

/-- Combining actual coupling identification with full mass of the root law
discharges the mass-identification premise of the telescoping theorem. -/
theorem l1_limit_full_mass_of_same_source
    {Source : Type*} [MeasurableSpace Source]
    (source : Measure Source) [IsFiniteMeasure source]
    (observables : ℕ → Source → ℝ) (root : Source → ℝ)
    (observables_measurable : ∀ depth, Measurable (observables depth))
    (root_measurable : Measurable root)
    (pointwise : ∀ᵐ sample ∂source,
      Tendsto (fun depth => observables depth sample) atTop (𝓝 (root sample)))
    (kernels : ℕ → Lp ℝ 1 volume) (density : Lp ℝ 1 volume)
    (kernels_nonnegative : ∀ depth, 0 ≤ kernels depth)
    (kernel_laws : ∀ depth, source.map (observables depth) =
      volume.withDensity (fun point => ENNReal.ofReal (kernels depth point)))
    (convergence : Tendsto kernels atTop (𝓝 density))
    (parameters : Set ℝ) (parameters_measurable : MeasurableSet parameters)
    (root_mass : source.map root parameters = 1) :
    ∫ point in parameters, density point = 1 := by
  have identified := l1_limit_eq_root_law_of_same_source source observables root
    observables_measurable root_measurable pointwise kernels density
    kernels_nonnegative kernel_laws convergence
  rw [setIntegral_eq_real_measure_of_density (source.map root) density
    ((isClosed_Ici : IsClosed (Set.Ici (0 : Lp ℝ 1 volume))).mem_of_tendsto
      convergence (Eventually.of_forall kernels_nonnegative))
    identified parameters parameters_measurable,
    measureReal_def, root_mass, ENNReal.toReal_one]

end LambdaCantor.AE
