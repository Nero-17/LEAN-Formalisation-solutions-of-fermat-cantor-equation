import LambdaCantor.First.RootsConditionalDensities
import LambdaCantor.First.RootsL1Convergence

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction
namespace LambdaCantor.First.Roots

/-- Uniqueness of a nonnegative L1 limit from its bounded continuous tests. -/
theorem L1_limit_identified_by_bounded_tests
    (sequence : ℕ → Lp ℝ 1 volume) (limit : Lp ℝ 1 volume)
    (nonnegative : ∀ depth, 0 ≤ sequence depth)
    (convergence : Tendsto sequence atTop (𝓝 limit))
    (density : ℝ → ℝ) (density_nonnegative : ∀ point, 0 ≤ density point)
    (density_measurable : Measurable density) (density_integrable : Integrable density volume)
    (tests : ∀ test : ℝ →ᵇ ℝ,
      Tendsto (fun depth => ∫ point, test point * sequence depth point) atTop
        (𝓝 (∫ point, test point * density point))) :
    limit = density_integrable.toL1 density := by
  have limit_nonnegative : (0 : Lp ℝ 1 (volume : Measure ℝ)) ≤ limit := by
    have closed_nonnegative : IsClosed (Set.Ici (0 : Lp ℝ 1 (volume : Measure ℝ))) := isClosed_Ici
    exact closed_nonnegative.mem_of_tendsto convergence (Filter.Eventually.of_forall nonnegative)
  have limit_integrable : Integrable (limit : ℝ → ℝ) volume :=
    memLp_one_iff_integrable.mp (Lp.memLp limit)
  let representative : ℝ → ℝ := fun point => max (limit_integrable.aestronglyMeasurable.mk limit point) 0
  have representative_measurable : Measurable representative :=
    limit_integrable.aestronglyMeasurable.stronglyMeasurable_mk.measurable.max measurable_const
  have representative_nonnegative : ∀ point, 0 ≤ representative point := fun _ => le_max_right _ _
  have representative_eq : representative =ᵐ[volume] (limit : ℝ → ℝ) := by
    filter_upwards [limit_integrable.aestronglyMeasurable.ae_eq_mk,
      (Lp.coeFn_nonneg limit).mpr limit_nonnegative] with point equality positive
    change (0 : ℝ) ≤ (limit : ℝ → ℝ) point at positive
    simp only [representative, ← equality, max_eq_left positive]
  have representative_integrable := limit_integrable.congr representative_eq.symm
  let firstMeasure := volume.withDensity (fun point => ENNReal.ofReal (representative point))
  let secondMeasure := volume.withDensity (fun point => ENNReal.ofReal (density point))
  have first_finite : IsFiniteMeasure firstMeasure := by
    constructor
    rw [show firstMeasure = volume.withDensity (fun point => ENNReal.ofReal (representative point)) from rfl,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal representative_integrable
        (Filter.Eventually.of_forall representative_nonnegative)]
    exact ENNReal.ofReal_lt_top
  have second_finite : IsFiniteMeasure secondMeasure := by
    constructor
    rw [show secondMeasure = volume.withDensity (fun point => ENNReal.ofReal (density point)) from rfl,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal density_integrable
        (Filter.Eventually.of_forall density_nonnegative)]
    exact ENNReal.ofReal_lt_top
  have equality : (⟨firstMeasure, first_finite⟩ : FiniteMeasure ℝ) = ⟨secondMeasure, second_finite⟩ := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro test
    have identification := tendsto_nhds_unique (L1_bounded_test_tendsto sequence limit convergence test)
      (tests test)
    change (∫ point, test point ∂firstMeasure) = ∫ point, test point ∂secondMeasure
    dsimp [firstMeasure, secondMeasure]
    rw [integral_withDensity_eq_integral_toReal_smul representative_measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
      integral_withDensity_eq_integral_toReal_smul density_measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    calc
      _ = ∫ point, test point * limit point := by
        apply integral_congr_ae
        filter_upwards [representative_eq] with point equality
        rw [ENNReal.toReal_ofReal (representative_nonnegative point), smul_eq_mul, equality, mul_comm]
      _ = ∫ point, test point * density point := identification
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun point => by
          change test point * density point = (ENNReal.ofReal (density point)).toReal • test point
          rw [ENNReal.toReal_ofReal (density_nonnegative point), smul_eq_mul, mul_comm])
  have density_eq : representative =ᵐ[volume] density :=
    nonnegative_density_unique (measure := firstMeasure) representative density representative_nonnegative density_nonnegative
      representative_measurable density_measurable rfl
      (congrArg (fun measure : FiniteMeasure ℝ => (measure : Measure ℝ)) equality)
  apply Lp.ext
  filter_upwards [representative_eq, density_eq, density_integrable.coeFn_toL1] with point first second third
  exact first.symm.trans (second.trans third.symm)

def selectedWeightedKernelLaw {exponent : ℝ} (data : RootFibreData exponent)
    (selected : Set (ℕ → Bool × Bool)) (weight : ℝ≥0∞) (depth : ℕ) : Measure ℝ :=
  weight • ((pairedAddressMeasure.restrict (prefixNeighborhood selected depth)).map
    (selectedRootKernel data selected depth))

theorem selectedWeightedKernel_density {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound : ℕ) (selected : Set (ℕ → Bool × Bool))
    (selected_subset : selected ⊆ rootSobolevGoodSet data orderIndex bound)
    (weight : ℝ≥0∞) (weight_finite : weight ≠ ∞) (depth : ℕ) :
    LinearRegularity.HasL2Density (selectedWeightedKernelLaw data selected weight depth) := by
  apply hasL2Density_smul _ weight weight_finite
  apply selectedRootKernel_law_hasL2Density
  intro representative member
  exact rootSobolevGoodSet_projected_density data orderIndex bound representative (selected_subset member)

def selectedWeightedKernelL1 {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound : ℕ) (selected : Set (ℕ → Bool × Bool))
    (selected_subset : selected ⊆ rootSobolevGoodSet data orderIndex bound)
    (weight : ℝ≥0∞) (weight_finite : weight ≠ ∞) (depth : ℕ) : Lp ℝ 1 (volume : Measure ℝ) :=
  measureDensityL1 _ (selectedWeightedKernel_density data orderIndex bound selected selected_subset weight weight_finite depth)

theorem selectedWeightedKernelLaw_mass {exponent : ℝ} (data : RootFibreData exponent)
    (selected : Set (ℕ → Bool × Bool)) (weight : ℝ≥0∞) (depth : ℕ) :
    (selectedWeightedKernelLaw data selected weight depth).real Set.univ =
      weight.toReal * pairedAddressMeasure.real (prefixNeighborhood selected depth) := by
  unfold selectedWeightedKernelLaw
  rw [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    Measure.map_apply (continuous_selectedRootKernel data selected depth).measurable MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ]
  rfl

/-- Weighted local kernels converge once their actual retained replacement
estimate is supplied. This interface is applied to the one fixed global good
set intersected with a prefix; it does not change the good-set constants. -/
theorem selectedWeightedKernelL1_converges {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound : ℕ) (selected : Set (ℕ → Bool × Bool))
    (selected_subset : selected ⊆ rootSobolevGoodSet data orderIndex bound)
    (weight : ℝ≥0∞) (weight_finite : weight ≠ ∞)
    (rate : ℕ → ℝ) (rate_summable : Summable rate) (minimumDepth : ℕ)
    (replacement : ∀ depth, minimumDepth ≤ depth →
      ∃ retained_exists : LinearRegularity.HasL2Density
        (weight • ((pairedAddressMeasure.restrict (prefixNeighborhood selected (depth + 1))).map
          (selectedRootKernel data selected depth))),
        ‖selectedWeightedKernelL1 data orderIndex bound selected selected_subset weight weight_finite (depth + 1) -
          measureDensityL1 _ retained_exists‖ ≤ rate depth) :
    ∃ limit : Lp ℝ 1 volume,
      Tendsto (selectedWeightedKernelL1 data orderIndex bound selected selected_subset weight weight_finite)
        atTop (𝓝 limit) := by
  let massLoss := fun depth : ℕ => weight.toReal *
    (pairedAddressMeasure.real (prefixNeighborhood selected depth) -
      pairedAddressMeasure.real (prefixNeighborhood selected (depth + 1)))
  have losses_summable : Summable massLoss :=
    (prefixNeighborhood_deleted_mass_summable selected).mul_left weight.toReal
  have step_bound (depth : ℕ) (depth_ge : minimumDepth ≤ depth) :
      ‖selectedWeightedKernelL1 data orderIndex bound selected selected_subset weight weight_finite (depth + 1) -
        selectedWeightedKernelL1 data orderIndex bound selected selected_subset weight weight_finite depth‖ ≤
      massLoss depth + rate depth := by
    obtain ⟨retained_exists, replacement_bound⟩ := replacement depth depth_ge
    have dominated : weight • ((pairedAddressMeasure.restrict (prefixNeighborhood selected (depth + 1))).map
        (selectedRootKernel data selected depth)) ≤ selectedWeightedKernelLaw data selected weight depth := by
      apply _root_.smul_le_smul_left
      exact Measure.map_mono
        (Measure.restrict_mono_set _ (prefixNeighborhood_antitone selected (Nat.le_succ depth)))
        (continuous_selectedRootKernel data selected depth).measurable
    have deletion_cost := measureDensityL1_distance_of_le retained_exists
      (selectedWeightedKernel_density data orderIndex bound selected selected_subset weight weight_finite depth) dominated
    rw [selectedWeightedKernelLaw_mass] at deletion_cost
    have retained_mass : (weight • ((pairedAddressMeasure.restrict (prefixNeighborhood selected (depth + 1))).map
        (selectedRootKernel data selected depth))).real Set.univ =
        weight.toReal * pairedAddressMeasure.real (prefixNeighborhood selected (depth + 1)) := by
      rw [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
        Measure.map_apply (continuous_selectedRootKernel data selected depth).measurable MeasurableSet.univ,
        Set.preimage_univ, Measure.restrict_apply_univ]
      rfl
    rw [retained_mass] at deletion_cost
    calc
      _ ≤ ‖selectedWeightedKernelL1 data orderIndex bound selected selected_subset weight weight_finite (depth + 1) -
          measureDensityL1 _ retained_exists‖ +
          ‖measureDensityL1 _ retained_exists -
            selectedWeightedKernelL1 data orderIndex bound selected selected_subset weight weight_finite depth‖ := by
        simpa only [dist_eq_norm] using dist_triangle
          (selectedWeightedKernelL1 data orderIndex bound selected selected_subset weight weight_finite (depth + 1))
          (measureDensityL1 _ retained_exists)
          (selectedWeightedKernelL1 data orderIndex bound selected selected_subset weight weight_finite depth)
      _ ≤ rate depth + massLoss depth := by
        apply add_le_add replacement_bound
        rw [norm_sub_rev]
        dsimp [massLoss]
        rw [mul_sub]
        exact deletion_cost.le
      _ = _ := add_comm _ _
  have shifted_cauchy : CauchySeq (fun depth => selectedWeightedKernelL1 data orderIndex bound selected selected_subset
      weight weight_finite (depth + minimumDepth)) := by
    apply cauchySeq_of_dist_le_of_summable (fun depth => massLoss (depth + minimumDepth) + rate (depth + minimumDepth))
    · intro depth
      rw [dist_comm, dist_eq_norm]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        step_bound (depth + minimumDepth) (by omega)
    · exact (summable_nat_add_iff minimumDepth).mpr (losses_summable.add rate_summable)
  obtain ⟨limit, convergence⟩ := cauchySeq_tendsto_of_complete shifted_cauchy
  exact ⟨limit, (tendsto_add_atTop_iff_nat minimumDepth).mp convergence⟩

/-- Weak root linearization identifies every local L1 kernel limit with the
actual weighted restricted-root density. -/
theorem selectedWeightedKernelL1_limit_identification {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound : ℕ) (selected : Set (ℕ → Bool × Bool))
    (selected_subset : selected ⊆ rootSobolevGoodSet data orderIndex bound) (closed : IsClosed selected)
    (weight : ℝ≥0∞) (weight_finite : weight ≠ ∞)
    (limit : Lp ℝ 1 volume)
    (convergence : Tendsto (selectedWeightedKernelL1 data orderIndex bound selected selected_subset weight weight_finite)
      atTop (𝓝 limit))
    (density : ℝ → ℝ) (nonnegative : ∀ point, 0 ≤ density point)
    (measurable : Measurable density) (integrable : Integrable density volume)
    (law : weight • ((pairedAddressMeasure.restrict selected).map data.root) =
      volume.withDensity (fun point => ENNReal.ofReal (density point))) :
    limit = integrable.toL1 density := by
  apply L1_limit_identified_by_bounded_tests _ limit
    (fun depth => measureDensityL1_nonnegative _ _) convergence density nonnegative measurable integrable
  intro test
  have weak := (prefixNeighborhood_kernel_integral_tendsto data selected closed test test.continuous
    ‖test‖ test.norm_coe_le_norm).const_mul weight.toReal
  have sequence_identity : (fun depth => ∫ point, test point *
      selectedWeightedKernelL1 data orderIndex bound selected selected_subset weight weight_finite depth point) =
      (fun depth => weight.toReal * ∫ digits, (prefixNeighborhood selected depth).indicator
        (fun other => test (selectedRootKernel data selected depth other)) digits ∂pairedAddressMeasure) := by
    funext depth
    rw [selectedWeightedKernelL1, measureDensityL1_test_integral]
    unfold selectedWeightedKernelLaw
    rw [integral_smul_measure, integral_map (continuous_selectedRootKernel data selected depth).measurable.aemeasurable
      test.continuous.measurable.aestronglyMeasurable,
      integral_indicator (measurableSet_prefixNeighborhood selected depth)]
    rfl
  have target_identity : (∫ point, test point * density point) = weight.toReal *
      ∫ digits, selected.indicator (fun other => test (data.root other)) digits ∂pairedAddressMeasure := by
    have integral_law := congrArg (fun measure : Measure ℝ => ∫ point, test point ∂measure) law
    rw [integral_smul_measure, integral_map (rootFibreData_continuous_root data).measurable.aemeasurable
      test.continuous.measurable.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul measurable.ennreal_ofReal
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))] at integral_law
    rw [integral_indicator closed.measurableSet]
    exact (integral_law.trans (integral_congr_ae (Filter.Eventually.of_forall (fun point => by
      change (ENNReal.ofReal (density point)).toReal • test point = test point * density point
      rw [ENNReal.toReal_ofReal (nonnegative point), smul_eq_mul, mul_comm])))).symm
  rw [← sequence_identity, ← target_identity] at weak
  exact weak

/-- The normalized local density chosen through disintegration is the L1
limit of the actual local complete-kernel sums. -/
theorem goodSetPrefixLocalKernel_tendsto {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound prefixDepth : ℕ) (word : Fin prefixDepth → Bool × Bool)
    (rate : ℕ → ℝ) (rate_summable : Summable rate) (minimumDepth : ℕ)
    (replacement : ∀ depth, minimumDepth ≤ depth →
      ∃ retained_exists : LinearRegularity.HasL2Density
        (((4 : ℝ≥0∞) ^ prefixDepth) • ((pairedAddressMeasure.restrict (prefixNeighborhood
          (rootSobolevGoodSet data orderIndex bound ∩ finitePairedPrefix word) (depth + 1))).map
            (selectedRootKernel data (rootSobolevGoodSet data orderIndex bound ∩ finitePairedPrefix word) depth))),
        ‖selectedWeightedKernelL1 data orderIndex bound
          (rootSobolevGoodSet data orderIndex bound ∩ finitePairedPrefix word) Set.inter_subset_left
          ((4 : ℝ≥0∞) ^ prefixDepth) (by finiteness) (depth + 1) -
            measureDensityL1 _ retained_exists‖ ≤ rate depth) :
    Tendsto (selectedWeightedKernelL1 data orderIndex bound
      (rootSobolevGoodSet data orderIndex bound ∩ finitePairedPrefix word) Set.inter_subset_left
      ((4 : ℝ≥0∞) ^ prefixDepth) (by finiteness)) atTop
      (𝓝 ((goodSetPrefixDensity_properties data orderIndex bound prefixDepth word).2.2.toL1
        (goodSetPrefixDensity data orderIndex bound prefixDepth word))) := by
  obtain ⟨limit, convergence⟩ := selectedWeightedKernelL1_converges data orderIndex bound
    (rootSobolevGoodSet data orderIndex bound ∩ finitePairedPrefix word) Set.inter_subset_left
    ((4 : ℝ≥0∞) ^ prefixDepth) (by finiteness) rate rate_summable minimumDepth replacement
  have prefix_closed : IsClosed (finitePairedPrefix word) := by
    have equality : finitePairedPrefix word =
        (fun digits : ℕ → Bool × Bool => fun index : Fin prefixDepth => digits index) ⁻¹' {word} := by
      ext digits
      simp only [finitePairedPrefix, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
    rw [equality]
    exact isClosed_singleton.preimage (by fun_prop)
  have actual_law : ((4 : ℝ≥0∞) ^ prefixDepth) •
      ((pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound ∩ finitePairedPrefix word)).map data.root) =
      volume.withDensity (fun point => ENNReal.ofReal (goodSetPrefixDensity data orderIndex bound prefixDepth word point)) := by
    have law := goodSetPrefixDensity_law data orderIndex bound prefixDepth word
    rw [Measure.restrict_restrict (measurableSet_finitePairedPrefix word), Set.inter_comm] at law
    exact law
  have identification := selectedWeightedKernelL1_limit_identification data orderIndex bound
    (rootSobolevGoodSet data orderIndex bound ∩ finitePairedPrefix word) Set.inter_subset_left
    ((rootFibreData_compact_good_set data orderIndex bound).isClosed.inter prefix_closed)
    ((4 : ℝ≥0∞) ^ prefixDepth) (by finiteness) limit convergence
    (goodSetPrefixDensity data orderIndex bound prefixDepth word)
    (goodSetPrefixDensity_properties data orderIndex bound prefixDepth word).1
    (goodSetPrefixDensity_properties data orderIndex bound prefixDepth word).2.1
    (goodSetPrefixDensity_properties data orderIndex bound prefixDepth word).2.2 actual_law
  rwa [identification] at convergence

end LambdaCantor.First.Roots
