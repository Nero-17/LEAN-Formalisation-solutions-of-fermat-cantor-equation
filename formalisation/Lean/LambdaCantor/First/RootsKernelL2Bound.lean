import LambdaCantor.First.RootsL1Refinement
import LambdaCantor.First.RootsDensityEnergyReal
import LambdaCantor.First.RootsKernelScaleBounds

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace LambdaCantor.First.Roots

/-- Quantitative L2 control follows from the already isolated forward
Plancherel input and the actual characteristic-energy bound. -/
theorem density_square_le_weighted_characteristic_energy (measure : Measure ℝ) [IsFiniteMeasure measure]
    (density : ℝ → ℝ) (nonnegative : ∀ point, 0 ≤ density point)
    (measurable : Measurable density) (integrable : Integrable density volume)
    (square : MemLp density 2 volume)
    (law : measure = volume.withDensity (fun point => ENNReal.ofReal (density point)))
    (order bound : ℝ) (order_nonnegative : 0 ≤ order) (bound_nonnegative : 0 ≤ bound)
    (energy : (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ order *
      ‖charFun measure frequency‖ ^ 2)) ≤ ENNReal.ofReal bound) :
    (∫ point, density point ^ 2) ≤ (2 : ℝ) ^ order * bound := by
  have plancherel := External.classical_plancherel_l1_l2
    (fun point => (density point : ℂ)) integrable.ofReal square.ofReal
  have unweighted_integrable := plancherel.1.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have weighted_integrable := density_fourier_weighted_integrable measure density nonnegative
    measurable law order order_nonnegative (ne_top_of_le_ne_top ENNReal.ofReal_ne_top energy)
  calc
    _ = ∫ point, ‖(density point : ℂ)‖ ^ 2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun point => by simp)
    _ = ∫ frequency, ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
        (fun point => (density point : ℂ)) frequency‖ ^ 2 := plancherel.2.symm
    _ ≤ ∫ frequency, (1 + frequency ^ 2) ^ order *
        ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
          (fun point => (density point : ℂ)) frequency‖ ^ 2 := by
      apply integral_mono unweighted_integrable weighted_integrable
      intro frequency
      have weight := Real.one_le_rpow (show 1 ≤ 1 + frequency ^ 2 by nlinarith [sq_nonneg frequency])
        order_nonnegative
      simpa only [one_mul] using mul_le_mul_of_nonneg_right weight (sq_nonneg _)
    _ ≤ _ := density_fourier_weighted_real_bound measure density nonnegative measurable law order bound
      order_nonnegative bound_nonnegative energy

/-- The exact square integral scaling of an actual affine density. -/
theorem affineDensity_square_integral (center scale : ℝ) (scale_nonzero : scale ≠ 0)
    (density : ℝ → ℝ) :
    (∫ point, affineDensity center scale density point ^ 2) =
      |scale|⁻¹ * ∫ point, density point ^ 2 := by
  have transformed : (∫ point, density ((point - center) / scale) ^ 2) =
      |scale| * ∫ point, density point ^ 2 := by
    rw [integral_sub_right_eq_self (fun point : ℝ => density (point / scale) ^ 2) center]
    simpa only [smul_eq_mul] using
      (Measure.integral_comp_div (fun point : ℝ => density point ^ 2) scale)
  simp only [affineDensity, mul_pow]
  rw [integral_const_mul, transformed]
  field_simp [abs_ne_zero.mpr scale_nonzero]
  <;> ring

/-- Frozen kernels have a uniform L2 square bound at their actual root
scale, rather than at the much coarser lower endpoint of the parameter band. -/
theorem rootSobolevGoodSet_frozen_kernel_square_bound {exponent : ℝ}
    (data : RootFibreData exponent) (orderIndex bound : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (representative : ℕ → Bool × Bool), representative ∈ rootSobolevGoodSet data orderIndex bound →
        ∀ depth : ℕ, ∃ density : ℝ → ℝ,
          (∀ point, 0 ≤ density point) ∧ Measurable density ∧ Integrable density volume ∧
          MemLp density 2 volume ∧
          completeRootKernelLaw data representative depth =
            volume.withDensity (fun point => ENNReal.ofReal (density point)) ∧
          (∫ point, density point ^ 2) ≤ constant / data.root representative ^ depth := by
  obtain ⟨lowerScale, upperScale, lower_positive, upper_positive, scales⟩ :=
    rootKernelVertical_uniform_normalization data
  let order : ℝ := 1 / ((orderIndex : ℝ) + 1)
  let energyConstant : ℝ := (2 : ℝ) ^ order * bound
  refine ⟨energyConstant / lowerScale, by dsimp [energyConstant]; positivity, ?_⟩
  intro representative member depth
  let projected := pairedAddressMeasure.map (projectedRootModel (rootFibreState data representative))
  have projected_finite : IsFiniteMeasure projected := by dsimp [projected]; infer_instance
  have projected_exists := rootSobolevGoodSet_projected_density data orderIndex bound representative member
  let projectedDensity := measureDensity projected projected_exists
  have properties := measureDensity_properties projected projected_exists
  have projected_square : (∫ point, projectedDensity point ^ 2) ≤ energyConstant := by
    apply density_square_le_weighted_characteristic_energy projected projectedDensity
      properties.1 properties.2.1 properties.2.2.1 properties.2.2.2.1 properties.2.2.2.2
      order bound (by dsimp [order]; positivity) (by positivity)
    simpa only [rootSobolevGoodSet, Set.mem_setOf_eq, projectedSobolevEnergy, order, projected, ENNReal.ofReal_natCast] using member
  let center : ℝ := data.root representative + rootKernelHorizontal data representative depth *
      address (data.root representative) (fun index => (representative (index + depth)).1) +
    rootKernelVertical data representative depth *
      address (data.root representative) (fun index => (representative (index + depth)).2)
  let scale : ℝ := -rootKernelVertical data representative depth
  have scale_nonzero : scale ≠ 0 := neg_ne_zero.mpr (rootKernelVertical_ne_zero data representative depth)
  have root_positive : 0 < data.root representative := by
    linarith [data.lower_gt_quarter, (data.root_in_band representative).1]
  have root_power_positive : 0 < data.root representative ^ depth := pow_pos root_positive depth
  have scale_lower : lowerScale * data.root representative ^ depth ≤ |scale| := by
    have lower := (scales representative depth).1
    rw [abs_div, abs_of_pos root_power_positive] at lower
    simpa only [scale, abs_neg] using (le_div_iff₀ root_power_positive).mp lower
  refine ⟨affineDensity center scale projectedDensity, ?_, ?_,
    affineDensity_integrable center scale scale_nonzero _ properties.2.2.1,
    affineDensity_memLp_two center scale scale_nonzero _ properties.2.1 properties.2.2.2.1, ?_, ?_⟩
  · intro point
    exact mul_nonneg (inv_nonneg.mpr (abs_nonneg scale)) (properties.1 _)
  · unfold affineDensity
    exact measurable_const.mul (properties.2.1.comp (by fun_prop))
  · rw [completeRootKernelLaw_rootModel]
    have affine_law := affine_map_withDensity center scale scale_nonzero projectedDensity properties.2.1
    rw [← properties.2.2.2.2] at affine_law
    convert affine_law using 1
    congr 1
    funext point
    dsimp [center, scale]
    ring
  · rw [affineDensity_square_integral center scale scale_nonzero]
    calc
      _ ≤ |scale|⁻¹ * energyConstant := mul_le_mul_of_nonneg_left projected_square (by positivity)
      _ ≤ (energyConstant / lowerScale) / data.root representative ^ depth := by
        have reciprocal := one_div_le_one_div_of_le
          (mul_pos lower_positive root_power_positive) scale_lower
        have energy_nonnegative : 0 ≤ energyConstant := by dsimp [energyConstant]; positivity
        calc
          |scale|⁻¹ * energyConstant = energyConstant * (1 / |scale|) := by
            rw [one_div, mul_comm]
          _ ≤ energyConstant * (1 / (lowerScale * data.root representative ^ depth)) :=
            mul_le_mul_of_nonneg_left reciprocal energy_nonnegative
          _ = (energyConstant / lowerScale) / data.root representative ^ depth := by
            rw [div_div]
            simp only [one_div, div_eq_mul_inv, one_mul]

/-- The square bound is independent of the pointwise choice of an actual
nonnegative density. This also applies to the representative used by the
one-sided prefix envelope. -/
theorem rootSobolevGoodSet_frozen_kernel_square_bound_of_density {exponent : ℝ}
    (data : RootFibreData exponent) (orderIndex bound : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (representative : ℕ → Bool × Bool),
        representative ∈ rootSobolevGoodSet data orderIndex bound → ∀ depth : ℕ,
        ∀ density : ℝ → ℝ, (∀ point, 0 ≤ density point) → Measurable density →
          completeRootKernelLaw data representative depth =
            volume.withDensity (fun point => ENNReal.ofReal (density point)) →
          (∫ point, density point ^ 2) ≤ constant / data.root representative ^ depth := by
  obtain ⟨constant, nonnegative, estimate⟩ :=
    rootSobolevGoodSet_frozen_kernel_square_bound data orderIndex bound
  refine ⟨constant, nonnegative, ?_⟩
  intro representative member depth density density_nonnegative density_measurable density_law
  obtain ⟨chosenDensity, chosen_nonnegative, chosen_measurable, _, _, chosen_law, chosen_bound⟩ :=
    estimate representative member depth
  have equality := nonnegative_density_unique density chosenDensity
    density_nonnegative chosen_nonnegative density_measurable chosen_measurable
    density_law chosen_law
  calc
    (∫ point, density point ^ 2) = ∫ point, chosenDensity point ^ 2 := by
      apply integral_congr_ae
      filter_upwards [equality] with point equality
      rw [equality]
    _ ≤ _ := chosen_bound

end LambdaCantor.First.Roots
