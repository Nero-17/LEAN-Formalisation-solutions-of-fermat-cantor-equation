import LambdaCantor.First.Roots
import LambdaCantor.First.RootsConditionalBorelCantelli
import LambdaCantor.First.RootsL1Refinement
import LambdaCantor.First.RootsConvergence
import LambdaCantor.First.RootsKernelL2Bound
import LambdaCantor.First.RootsPrefixLocalLimit
import LambdaCantor.First.RootsPrefixSupport
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators Classical
namespace LambdaCantor.First.Roots

/-- The one-sided envelope can be constructed inside the genuine L1 Banach
lattice. Deletion is used only through retained≤parent, so it incurs no
second payment in the upper envelope. -/
theorem L1_refinement_one_sided_envelope
    {space : Type*} [NormedAddCommGroup space] [Lattice space] [HasSolidNorm space]
    [IsOrderedAddMonoid space] [CompleteSpace space]
    (kernels retained : ℕ → space) (limit : space)
    (convergence : Tendsto kernels atTop (𝓝 limit))
    (dominated : ∀ index, retained index ≤ kernels index)
    (rate : ℕ → ℝ) (rate_nonnegative : ∀ index, 0 ≤ rate index)
    (replacement : ∀ index, ‖kernels (index + 1) - retained index‖ ≤ rate index)
    (summable_rate : Summable rate) :
    ∃ error : space, 0 ≤ error ∧ limit ≤ kernels 0 + error ∧
      ‖error‖ ≤ ∑' index, rate index := by
  let errorTerm : ℕ → space := fun index => |kernels (index + 1) - retained index|
  have term_norm (index : ℕ) : ‖errorTerm index‖ ≤ rate index := by
    simpa only [errorTerm, norm_abs_eq_norm] using replacement index
  have summable_norm : Summable (fun index => ‖errorTerm index‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) term_norm summable_rate
  have summable_errors : Summable errorTerm := summable_norm.of_norm
  have finite_bound (depth : ℕ) :
      kernels depth ≤ kernels 0 + ∑ index ∈ Finset.range depth, errorTerm index := by
    induction depth with
    | zero => simp
    | succ depth induction_hypothesis =>
      rw [Finset.sum_range_succ]
      have single_step : kernels (depth + 1) ≤ retained depth + errorTerm depth := by
        have comparison := le_abs_self (kernels (depth + 1) - retained depth)
        dsimp only [errorTerm]
        simpa only [add_comm] using (sub_le_iff_le_add.mp comparison)
      calc
        _ ≤ retained depth + errorTerm depth := single_step
        _ ≤ kernels depth + errorTerm depth := _root_.add_le_add (dominated depth) (le_refl (errorTerm depth))
        _ ≤ (kernels 0 + ∑ index ∈ Finset.range depth, errorTerm index) + errorTerm depth :=
          _root_.add_le_add induction_hypothesis (le_refl (errorTerm depth))
        _ = _ := by abel
  refine ⟨∑' index, errorTerm index, tsum_nonneg (fun _ => abs_nonneg _), ?_, ?_⟩
  · exact le_of_tendsto_of_tendsto convergence
      (tendsto_const_nhds.add summable_errors.hasSum.tendsto_sum_nat)
      (Filter.Eventually.of_forall finite_bound)
  · exact (norm_tsum_le_tsum_norm summable_norm).trans
      (summable_norm.tsum_le_tsum term_norm summable_rate)

/-- Original Bernoulli word weights equal the actual retained source mass;
this identity makes localization to one fixed prefix preserve its factor. -/
theorem admissible_word_weights_mass {exponent : ℝ} (data : RootFibreData exponent)
    (selected : Set (ℕ → Bool × Bool)) (depth : ℕ) :
    (∑ word : Fin depth → Bool × Bool,
      (if ∃ representative ∈ selected, ∀ index : Fin depth, representative index = word index
        then (4 : ℝ≥0∞)⁻¹ ^ depth else 0).toReal) =
      pairedAddressMeasure.real (prefixNeighborhood selected depth) := by
  classical
  have kernel_mass (representative : ℕ → Bool × Bool) :
      completeRootKernelLaw data representative depth Set.univ = 1 := by
    letI := completeRootKernelLaw_probability data representative depth
    exact measure_univ
  have mass := congrArg (fun law : Measure ℝ => law Set.univ)
    (selectedRootKernel_law_eq_sum data selected depth)
  rw [Measure.map_apply (continuous_selectedRootKernel data selected depth).measurable
    MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ,
    Measure.finsetSum_apply] at mass
  have terms : (∑ word : Fin depth → Bool × Bool,
      (if ∃ representative ∈ selected, ∀ index : Fin depth, representative index = word index
        then ((4 : ℝ≥0∞)⁻¹ ^ depth) •
          completeRootKernelLaw data (prefixRepresentative selected depth word) depth else 0) Set.univ) =
      ∑ word : Fin depth → Bool × Bool,
        if ∃ representative ∈ selected, ∀ index : Fin depth, representative index = word index
          then (4 : ℝ≥0∞)⁻¹ ^ depth else 0 := by
    apply Finset.sum_congr rfl
    intro word _
    split_ifs <;> simp [Measure.smul_apply, kernel_mass]
  rw [terms] at mass
  rw [measureReal_def, mass, ENNReal.toReal_sum]
  intro word _
  split_ifs <;> finiteness

/-- The actual interpolation replacement rate has a quantitative geometric
polynomial tail. This is stronger than its summability alone. -/
theorem actual_replacement_rate_tail_bound
    (ratio order prefactor displacementConstant : ℝ)
    (ratio_positive : 0 < ratio) (ratio_lt_one : ratio < 1)
    (order_positive : 0 < order) (order_le_one : order ≤ 1)
    (prefactor_nonnegative : 0 ≤ prefactor) (displacement_nonnegative : 0 ≤ displacementConstant) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ depth : ℕ,
      (∑' index : ℕ, prefactor *
        (displacementConstant * (((depth + index : ℕ) : ℝ) + 1) * ratio ^ (depth + index)) ^ order) ≤
      constant * ((depth : ℝ) + 1) ^ order * ratio ^ (order * depth) := by
  let basicRate : ℕ → ℝ := fun index => ((index : ℝ) + 1) ^ order * ratio ^ (order * index)
  have basic_summable : Summable basicRate :=
    summable_replacement_rate ratio order ratio_positive.le ratio_lt_one order_positive order_le_one
  have actual_summable := summable_actual_replacement_rate ratio order prefactor displacementConstant
    ratio_positive.le ratio_lt_one order_positive order_le_one displacement_nonnegative
  refine ⟨prefactor * displacementConstant ^ order * ∑' index, basicRate index, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg prefactor_nonnegative
      (Real.rpow_nonneg displacement_nonnegative _)) (tsum_nonneg (fun _ => by dsimp [basicRate]; positivity))
  · intro depth
    let factor : ℝ := prefactor * displacementConstant ^ order *
      ((depth : ℝ) + 1) ^ order * ratio ^ (order * depth)
    have factor_nonnegative : 0 ≤ factor := by dsimp [factor]; positivity
    have term_bound (index : ℕ) : prefactor *
        (displacementConstant * (((depth + index : ℕ) : ℝ) + 1) * ratio ^ (depth + index)) ^ order ≤
        factor * basicRate index := by
      have polynomial : (((depth + index : ℕ) : ℝ) + 1) ≤
          ((depth : ℝ) + 1) * ((index : ℝ) + 1) := by
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) depth, Nat.cast_nonneg (α := ℝ) index]
      calc
        _ ≤ prefactor *
          (displacementConstant * (((depth : ℝ) + 1) * ((index : ℝ) + 1)) *
            ratio ^ (depth + index)) ^ order := by
          apply mul_le_mul_of_nonneg_left _ prefactor_nonnegative
          apply Real.rpow_le_rpow (by positivity) _ order_positive.le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left polynomial displacement_nonnegative) (by positivity)
        _ = factor * basicRate index := by
          rw [pow_add]
          rw [Real.mul_rpow (by positivity : 0 ≤ displacementConstant *
              (((depth : ℝ) + 1) * ((index : ℝ) + 1)))
              (mul_nonneg (pow_nonneg ratio_positive.le depth) (pow_nonneg ratio_positive.le index)),
            Real.mul_rpow displacement_nonnegative (by positivity),
            Real.mul_rpow (by positivity : 0 ≤ (depth : ℝ) + 1) (by positivity : 0 ≤ (index : ℝ) + 1),
            Real.mul_rpow (pow_nonneg ratio_positive.le depth) (pow_nonneg ratio_positive.le index)]
          have power_identity (length : ℕ) : (ratio ^ length) ^ order = ratio ^ (order * length) := by
            rw [← Real.rpow_natCast ratio length, ← Real.rpow_mul ratio_positive.le]
            congr 1
            ring
          rw [power_identity depth, power_identity index]
          dsimp [factor, basicRate]
          ring
    have shifted_summable : Summable (fun index : ℕ => prefactor *
        (displacementConstant * (((depth + index : ℕ) : ℝ) + 1) * ratio ^ (depth + index)) ^ order) := by
      simpa only [Nat.add_comm] using (summable_nat_add_iff depth).mpr actual_summable
    calc
      _ ≤ ∑' index, factor * basicRate index :=
        shifted_summable.tsum_le_tsum term_bound
          (basic_summable.mul_left factor)
      _ = _ := by
        rw [tsum_mul_left]
        dsimp [factor]
        ring

/-- Actual retained replacement for any source subset of the one fixed
global good set. Its cost retains the exact source mass, which is essential
when only descendants of a fixed prefix are retained. -/
theorem rootSobolevGoodSet_subset_retained_L1_replacement
    {exponent : ℝ} (data : RootFibreData exponent) (orderIndex bound : ℕ) :
    ∃ prefactor displacementConstant : ℝ, 0 ≤ prefactor ∧ 0 < displacementConstant ∧
      ∃ minimumDepth : ℕ, ∀ selected : Set (ℕ → Bool × Bool),
        selected ⊆ rootSobolevGoodSet data orderIndex bound →
        ∀ depth, minimumDepth ≤ depth →
          ∃ (retained_exists : LinearRegularity.HasL2Density
              ((pairedAddressMeasure.restrict (prefixNeighborhood selected (depth + 1))).map
                (selectedRootKernel data selected depth)))
            (child_exists : LinearRegularity.HasL2Density
              ((pairedAddressMeasure.restrict (prefixNeighborhood selected (depth + 1))).map
                (selectedRootKernel data selected (depth + 1)))),
            ‖measureDensityL1 _ child_exists - measureDensityL1 _ retained_exists‖ ≤
              pairedAddressMeasure.real (prefixNeighborhood selected (depth + 1)) *
                (prefactor * (displacementConstant * ((depth : ℝ) + 1) * data.upper ^ depth) ^
                  (2 * (1 / ((orderIndex : ℝ) + 1)) / (3 + 2 * (1 / ((orderIndex : ℝ) + 1))))) := by
  classical
  obtain ⟨prefactor, displacementConstant, prefactor_nonnegative, displacement_positive,
    minimumDepth, pair_bound⟩ := rootSobolevGoodSet_parameter_L1_replacement data orderIndex bound
  refine ⟨prefactor, displacementConstant, prefactor_nonnegative, displacement_positive, minimumDepth, ?_⟩
  intro selected selected_subset depth depth_ge
  have upper_positive : 0 < data.upper := by linarith [data.lower_gt_quarter, data.ordered]
  let admissible := fun word : Fin (depth + 1) → Bool × Bool =>
    ∃ representative ∈ selected, ∀ index : Fin (depth + 1), representative index = word index
  let parentLaw := fun word : Fin (depth + 1) → Bool × Bool =>
    if admissible word then pairedAddressMeasure.map (fun tail => completeRootKernel data
      (prefixRepresentative selected depth (parentWord word)) depth
      (prependPairedDigit (word (Fin.last depth)) tail)) else 0
  let childLaw := fun word : Fin (depth + 1) → Bool × Bool =>
    if admissible word then completeRootKernelLaw data
      (prefixRepresentative selected (depth + 1) word) (depth + 1) else 0
  have branch_bound (word : Fin (depth + 1) → Bool × Bool) :
      ∃ (parent_exists : LinearRegularity.HasL2Density (parentLaw word))
        (child_exists : LinearRegularity.HasL2Density (childLaw word)),
        ‖measureDensityL1 _ parent_exists - measureDensityL1 _ child_exists‖ ≤ prefactor *
          (displacementConstant * ((depth : ℝ) + 1) * data.upper ^ depth) ^
            (2 * (1 / ((orderIndex : ℝ) + 1)) / (3 + 2 * (1 / ((orderIndex : ℝ) + 1)))) := by
    by_cases member : admissible word
    · obtain ⟨parent_good, child_good, agreement, last_digit⟩ :=
        refinement_representatives selected word member
      obtain ⟨parent_exists, child_exists, estimate⟩ := pair_bound
        (prefixRepresentative selected depth (parentWord word))
        (prefixRepresentative selected (depth + 1) word) depth depth_ge (selected_subset parent_good) (selected_subset child_good) agreement
      simp only [last_digit] at parent_exists estimate
      exact ⟨by simpa only [parentLaw, if_pos member] using parent_exists,
        by simpa only [childLaw, if_pos member] using child_exists,
        by simpa only [parentLaw, childLaw, if_pos member] using estimate⟩
    · refine ⟨by simpa only [parentLaw, if_neg member] using hasL2Density_zero,
        by simpa only [childLaw, if_neg member] using hasL2Density_zero, ?_⟩
      simp only [parentLaw, childLaw, if_neg member, sub_self, norm_zero]
      positivity
  choose parent_exists child_exists estimates using branch_bound
  let parent_sum_exists := hasL2Density_finset_sum Finset.univ
    (fun word => (if admissible word then (4 : ℝ≥0∞)⁻¹ ^ (depth + 1) else 0) • parentLaw word)
    (fun word _ => hasL2Density_smul (parent_exists word) _ (by finiteness))
  let child_sum_exists := hasL2Density_finset_sum Finset.univ
    (fun word => (if admissible word then (4 : ℝ≥0∞)⁻¹ ^ (depth + 1) else 0) • childLaw word)
    (fun word _ => hasL2Density_smul (child_exists word) _ (by finiteness))
  have parent_sum : (∑ word, (if admissible word then (4 : ℝ≥0∞)⁻¹ ^ (depth + 1) else 0) • parentLaw word) =
      (pairedAddressMeasure.restrict (prefixNeighborhood selected (depth + 1))).map
        (selectedRootKernel data selected depth) := by
    rw [retainedRootKernel_law_eq_sum]
    apply Finset.sum_congr rfl
    intro word _
    by_cases member : admissible word
    · simp only [admissible] at member
      simp only [parentLaw, admissible, if_pos member]
    · simp only [admissible] at member
      simp only [parentLaw, admissible, if_neg member, smul_zero]
  have child_sum : (∑ word, (if admissible word then (4 : ℝ≥0∞)⁻¹ ^ (depth + 1) else 0) • childLaw word) =
      ((pairedAddressMeasure.restrict (prefixNeighborhood selected (depth + 1))).map
        (selectedRootKernel data selected (depth + 1))) := by
    rw [selectedRootKernel_law_eq_sum]
    apply Finset.sum_congr rfl
    intro word _
    by_cases member : admissible word
    · simp only [admissible] at member
      simp only [childLaw, admissible, if_pos member]
    · simp only [admissible] at member
      simp only [childLaw, admissible, if_neg member, smul_zero]
  have retained_exists : LinearRegularity.HasL2Density
      ((pairedAddressMeasure.restrict (prefixNeighborhood selected (depth + 1))).map
        (selectedRootKernel data selected depth)) := parent_sum ▸ parent_sum_exists
  have selected_child_exists : LinearRegularity.HasL2Density
      ((pairedAddressMeasure.restrict (prefixNeighborhood selected (depth + 1))).map
        (selectedRootKernel data selected (depth + 1))) := child_sum ▸ child_sum_exists
  refine ⟨retained_exists, selected_child_exists, ?_⟩
  have estimate := finite_density_replacement_bound Finset.univ parentLaw childLaw parent_exists child_exists
    (fun word => if admissible word then (4 : ℝ≥0∞)⁻¹ ^ (depth + 1) else 0)
    (fun word => by split_ifs <;> finiteness) _
    (fun word _ => estimates word)
  rw [admissible_word_weights_mass data selected (depth + 1)] at estimate
  have transport_density (first second : Measure ℝ) (equality : first = second)
      (first_exists : LinearRegularity.HasL2Density first)
      (second_exists : LinearRegularity.HasL2Density second) :
      measureDensityL1 first first_exists = measureDensityL1 second second_exists := by
    cases equality
    rfl
  have parent_density := transport_density _ _ parent_sum parent_sum_exists retained_exists
  have child_density := transport_density _ _ child_sum child_sum_exists selected_child_exists
  rw [parent_density, child_density] at estimate
  simpa only [norm_sub_rev] using estimate

/-- Localize inside a fixed prefix of the one global good set. -/
def goodSetPrefixSelected {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound prefixDepth : ℕ) (word : Fin prefixDepth → Bool × Bool) :
    Set (ℕ → Bool × Bool) := rootSobolevGoodSet data orderIndex bound ∩ finitePairedPrefix word

theorem finitePairedPrefix_mass {depth : ℕ} (word : Fin depth → Bool × Bool) :
    pairedAddressMeasure (finitePairedPrefix word) = (4 : ℝ≥0∞)⁻¹ ^ depth := by
  have preimage : (fun digits : ℕ → Bool × Bool => fun index : Fin depth => digits index) ⁻¹' {word} =
      finitePairedPrefix word := by
    ext digits
    simp only [finitePairedPrefix, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
      funext_iff]
  rw [← pairedWordMeasure_singleton depth word, pairedWordMeasure,
    Measure.map_apply (by fun_prop) (measurableSet_singleton _), preimage]

theorem goodSetPrefixSelected_neighborhood_subset {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound prefixDepth depth : ℕ) (word : Fin prefixDepth → Bool × Bool)
    (deeper : prefixDepth ≤ depth) :
    prefixNeighborhood (goodSetPrefixSelected data orderIndex bound prefixDepth word) depth ⊆
      finitePairedPrefix word := by
  rintro digits ⟨representative, member, agreement⟩ index
  exact (agreement index (index.isLt.trans_le deeper)).symm.trans (member.2 index)

/-- Normalization by the prefix probability cancels its small retained mass.
The bound is uniform in the prefix depth and the selected word. -/
theorem goodSetPrefixSelected_normalized_mass_le {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound prefixDepth depth : ℕ) (word : Fin prefixDepth → Bool × Bool)
    (deeper : prefixDepth ≤ depth) :
    (4 : ℝ) ^ prefixDepth * pairedAddressMeasure.real
      (prefixNeighborhood (goodSetPrefixSelected data orderIndex bound prefixDepth word) depth) ≤ 1 := by
  have mass_bound := measureReal_mono (μ := pairedAddressMeasure)
    (goodSetPrefixSelected_neighborhood_subset data orderIndex bound prefixDepth depth word deeper)
  have prefix_mass : pairedAddressMeasure.real (finitePairedPrefix word) = (4 : ℝ)⁻¹ ^ prefixDepth := by
    rw [measureReal_def, finitePairedPrefix_mass]
    simp
  rw [prefix_mass] at mass_bound
  calc
    _ ≤ (4 : ℝ) ^ prefixDepth * (4 : ℝ)⁻¹ ^ prefixDepth :=
      mul_le_mul_of_nonneg_left mass_bound (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num

/-- The normalized local parent-child replacement estimate uses only the
original global good set and its original constants. -/
theorem rootSobolevGoodSet_prefix_retained_L1_replacement
    {exponent : ℝ} (data : RootFibreData exponent) (orderIndex bound : ℕ) :
    ∃ prefactor displacementConstant : ℝ, 0 ≤ prefactor ∧ 0 < displacementConstant ∧
      ∃ minimumDepth : ℕ, ∀ (prefixDepth : ℕ) (word : Fin prefixDepth → Bool × Bool)
        (depth : ℕ), minimumDepth ≤ depth → prefixDepth ≤ depth →
        ∃ (retained_exists : LinearRegularity.HasL2Density
          (((4 : ℝ≥0∞) ^ prefixDepth) •
            ((pairedAddressMeasure.restrict (prefixNeighborhood
              (goodSetPrefixSelected data orderIndex bound prefixDepth word) (depth + 1))).map
                (selectedRootKernel data (goodSetPrefixSelected data orderIndex bound prefixDepth word) depth))))
          (child_exists : LinearRegularity.HasL2Density
          (((4 : ℝ≥0∞) ^ prefixDepth) •
            ((pairedAddressMeasure.restrict (prefixNeighborhood
              (goodSetPrefixSelected data orderIndex bound prefixDepth word) (depth + 1))).map
                (selectedRootKernel data (goodSetPrefixSelected data orderIndex bound prefixDepth word) (depth + 1))))),
          ‖measureDensityL1 _ child_exists - measureDensityL1 _ retained_exists‖ ≤ prefactor *
            (displacementConstant * ((depth : ℝ) + 1) * data.upper ^ depth) ^
              (2 * (1 / ((orderIndex : ℝ) + 1)) / (3 + 2 * (1 / ((orderIndex : ℝ) + 1)))) := by
  obtain ⟨prefactor, displacementConstant, prefactor_nonnegative, displacement_positive,
    minimumDepth, replacement⟩ := rootSobolevGoodSet_subset_retained_L1_replacement data orderIndex bound
  refine ⟨prefactor, displacementConstant, prefactor_nonnegative, displacement_positive, minimumDepth, ?_⟩
  intro prefixDepth word depth depth_ge deeper
  have upper_nonnegative : 0 ≤ data.upper := by linarith [data.lower_gt_quarter, data.ordered]
  obtain ⟨retained_exists, child_exists, estimate⟩ := replacement
    (goodSetPrefixSelected data orderIndex bound prefixDepth word) (fun _ member => member.1) depth depth_ge
  refine ⟨hasL2Density_smul retained_exists _ (by finiteness),
    hasL2Density_smul child_exists _ (by finiteness), ?_⟩
  rw [measureDensityL1_smul child_exists _ (by finiteness),
    measureDensityL1_smul retained_exists _ (by finiteness), ← smul_sub, norm_smul]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofNat, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)]
  calc
    _ ≤ (4 : ℝ) ^ prefixDepth *
        (pairedAddressMeasure.real (prefixNeighborhood
          (goodSetPrefixSelected data orderIndex bound prefixDepth word) (depth + 1)) *
          (prefactor * (displacementConstant * ((depth : ℝ) + 1) * data.upper ^ depth) ^
            (2 * (1 / ((orderIndex : ℝ) + 1)) / (3 + 2 * (1 / ((orderIndex : ℝ) + 1)))))) :=
      mul_le_mul_of_nonneg_left estimate (by positivity)
    _ = ((4 : ℝ) ^ prefixDepth * pairedAddressMeasure.real (prefixNeighborhood
          (goodSetPrefixSelected data orderIndex bound prefixDepth word) (depth + 1))) *
          (prefactor * (displacementConstant * ((depth : ℝ) + 1) * data.upper ^ depth) ^
            (2 * (1 / ((orderIndex : ℝ) + 1)) / (3 + 2 * (1 / ((orderIndex : ℝ) + 1))))) := by ring
    _ ≤ _ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (goodSetPrefixSelected_normalized_mass_le data orderIndex bound prefixDepth (depth + 1) word
          (deeper.trans (Nat.le_succ depth))) (by positivity)


/-- Measure domination is preserved by the canonical L1 density choices. -/
theorem measureDensityL1_mono {first second : Measure ℝ}
    (first_exists : LinearRegularity.HasL2Density first)
    (second_exists : LinearRegularity.HasL2Density second) (dominated : first ≤ second) :
    measureDensityL1 first first_exists ≤ measureDensityL1 second second_exists := by
  have comparison : (measureDensityL1 first first_exists : ℝ → ℝ) ≤ᵐ[volume]
      (measureDensityL1 second second_exists : ℝ → ℝ) := by
    filter_upwards [measureDensity_mono first_exists second_exists dominated,
      (measureDensity_properties first first_exists).2.2.1.coeFn_toL1,
      (measureDensity_properties second second_exists).2.2.1.coeFn_toL1] with point comparison first_eq second_eq
    simpa only [measureDensityL1] using first_eq.trans_le (comparison.trans_eq second_eq.symm)
  exact (Lp.coeFn_le _ _).mp comparison

/-- Actual prefix-local densities have the positive L1 envelope with the
manuscript's quantitative rate. Every local approximation uses descendants
inside the same fixed global Sobolev good set. -/
theorem rootSobolevGoodSet_prefix_L1_envelope {exponent : ℝ}
    (data : RootFibreData exponent) (orderIndex bound : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∃ minimumDepth : ℕ,
      ∀ (prefixDepth : ℕ) (word : Fin prefixDepth → Bool × Bool), minimumDepth ≤ prefixDepth →
        ∃ error : Lp ℝ 1 (volume : Measure ℝ), 0 ≤ error ∧
          (goodSetPrefixDensity_properties data orderIndex bound prefixDepth word).2.2.toL1
            (goodSetPrefixDensity data orderIndex bound prefixDepth word) ≤
          selectedWeightedKernelL1 data orderIndex bound
            (goodSetPrefixSelected data orderIndex bound prefixDepth word) Set.inter_subset_left
            ((4 : ℝ≥0∞) ^ prefixDepth) (by finiteness) prefixDepth + error ∧
          ‖error‖ ≤ constant * ((prefixDepth : ℝ) + 1) ^
            (2 * (1 / ((orderIndex : ℝ) + 1)) / (3 + 2 * (1 / ((orderIndex : ℝ) + 1)))) *
            data.upper ^ ((2 * (1 / ((orderIndex : ℝ) + 1)) /
              (3 + 2 * (1 / ((orderIndex : ℝ) + 1)))) * prefixDepth) := by
  obtain ⟨prefactor, displacementConstant, prefactor_nonnegative, displacement_positive,
    minimumDepth, replacements⟩ := rootSobolevGoodSet_prefix_retained_L1_replacement data orderIndex bound
  let order : ℝ := 2 * (1 / ((orderIndex : ℝ) + 1)) / (3 + 2 * (1 / ((orderIndex : ℝ) + 1)))
  let rate : ℕ → ℝ := fun depth => prefactor *
    (displacementConstant * ((depth : ℝ) + 1) * data.upper ^ depth) ^ order
  have order_bounds := interpolation_exponent_bounds (1 / ((orderIndex : ℝ) + 1)) (by positivity)
  have upper_positive : 0 < data.upper := by linarith [data.lower_gt_quarter, data.ordered]
  have upper_one : data.upper < 1 := by linarith [data.upper_lt_half]
  have summable_rate : Summable rate := summable_actual_replacement_rate data.upper order prefactor
    displacementConstant upper_positive.le upper_one order_bounds.1 order_bounds.2 displacement_positive.le
  obtain ⟨constant, constant_nonnegative, tail_bound⟩ := actual_replacement_rate_tail_bound
    data.upper order prefactor displacementConstant upper_positive upper_one order_bounds.1 order_bounds.2
    prefactor_nonnegative displacement_positive.le
  refine ⟨constant, constant_nonnegative, minimumDepth, ?_⟩
  intro prefixDepth word prefix_ge
  let selected := goodSetPrefixSelected data orderIndex bound prefixDepth word
  let kernels : ℕ → Lp ℝ 1 (volume : Measure ℝ) := fun index => selectedWeightedKernelL1 data orderIndex bound
    selected Set.inter_subset_left ((4 : ℝ≥0∞) ^ prefixDepth) (by finiteness) (prefixDepth + index)
  have replacement_at (depth : ℕ) (depth_ge : max minimumDepth prefixDepth ≤ depth) :
      ∃ retained_exists : LinearRegularity.HasL2Density
          (((4 : ℝ≥0∞) ^ prefixDepth) • ((pairedAddressMeasure.restrict
            (prefixNeighborhood selected (depth + 1))).map (selectedRootKernel data selected depth))),
        ‖selectedWeightedKernelL1 data orderIndex bound selected Set.inter_subset_left
          ((4 : ℝ≥0∞) ^ prefixDepth) (by finiteness) (depth + 1) -
            measureDensityL1 _ retained_exists‖ ≤ rate depth := by
    obtain ⟨retained_exists, child_exists, estimate⟩ := replacements prefixDepth word depth
      ((le_max_left _ _).trans depth_ge) ((le_max_right _ _).trans depth_ge)
    exact ⟨retained_exists, estimate⟩
  have convergence := goodSetPrefixLocalKernel_tendsto data orderIndex bound prefixDepth word
    rate summable_rate (max minimumDepth prefixDepth) replacement_at
  have shifted_convergence : Tendsto kernels atTop
      (𝓝 ((goodSetPrefixDensity_properties data orderIndex bound prefixDepth word).2.2.toL1
        (goodSetPrefixDensity data orderIndex bound prefixDepth word))) := by
    simpa only [kernels, selected, goodSetPrefixSelected, Nat.add_comm] using
      (tendsto_add_atTop_iff_nat prefixDepth).mpr convergence
  have shifted_replacements (index : ℕ) := replacement_at (prefixDepth + index) (by omega)
  choose retained_exists estimates using shifted_replacements
  let retained : ℕ → Lp ℝ 1 (volume : Measure ℝ) := fun index => measureDensityL1 _ (retained_exists index)
  have dominated (index : ℕ) : retained index ≤ kernels index := by
    apply measureDensityL1_mono
    apply _root_.smul_le_smul_left
    exact Measure.map_mono
      (Measure.restrict_mono_set _ (prefixNeighborhood_antitone selected (Nat.le_succ (prefixDepth + index))))
      (continuous_selectedRootKernel data selected (prefixDepth + index)).measurable
  have shifted_summable : Summable (fun index : ℕ => rate (prefixDepth + index)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff prefixDepth).mpr summable_rate
  obtain ⟨error, error_nonnegative, envelope, error_norm⟩ := L1_refinement_one_sided_envelope
    kernels retained _ shifted_convergence dominated (fun index => rate (prefixDepth + index))
    (fun _ => by dsimp [rate]; positivity)
    (fun index => by simpa only [kernels, retained, Nat.add_assoc] using estimates index) shifted_summable
  refine ⟨error, error_nonnegative, ?_, error_norm.trans (tail_bound prefixDepth)⟩
  simpa only [kernels, Nat.add_zero] using envelope

/-- At the initial prefix depth the normalized local approximation is one
complete fresh-tail law, using the actual selected representative. -/
theorem goodSetPrefixSelected_initial_kernel_law {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound depth : ℕ) (word : Fin depth → Bool × Bool)
    (nonempty : (goodSetPrefixSelected data orderIndex bound depth word).Nonempty) :
    selectedWeightedKernelLaw data (goodSetPrefixSelected data orderIndex bound depth word)
      ((4 : ℝ≥0∞) ^ depth) depth =
    completeRootKernelLaw data
      (prefixRepresentative (goodSetPrefixSelected data orderIndex bound depth word) depth word) depth := by
  classical
  let selected := goodSetPrefixSelected data orderIndex bound depth word
  have admissible (other : Fin depth → Bool × Bool) :
      (∃ representative ∈ selected, ∀ index : Fin depth, representative index = other index) ↔ other = word := by
    constructor
    · rintro ⟨representative, member, agreement⟩
      funext index
      exact (agreement index).symm.trans (member.2 index)
    · rintro rfl
      obtain ⟨representative, member⟩ := nonempty
      exact ⟨representative, member, member.2⟩
  unfold selectedWeightedKernelLaw
  rw [selectedRootKernel_law_eq_sum]
  change ((4 : ℝ≥0∞) ^ depth) •
      (∑ other : Fin depth → Bool × Bool,
        if ∃ representative ∈ selected, ∀ index : Fin depth, representative index = other index then
          ((4 : ℝ≥0∞)⁻¹ ^ depth) • completeRootKernelLaw data (prefixRepresentative selected depth other) depth
        else 0) = completeRootKernelLaw data (prefixRepresentative selected depth word) depth
  simp only [admissible, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [smul_smul, ← mul_pow,
    ENNReal.mul_inv_cancel (by norm_num) (by finiteness), one_pow, one_smul]

/-- Every positive L1 element admits an everywhere nonnegative measurable
representative whose integral is exactly its L1 norm. -/
theorem nonnegative_L1_representative (element : Lp ℝ 1 (volume : Measure ℝ)) (positive : 0 ≤ element) :
    ∃ function : ℝ → ℝ, (∀ point, 0 ≤ function point) ∧ Measurable function ∧
      Integrable function volume ∧ function =ᵐ[volume] (element : ℝ → ℝ) ∧
      (∫ point, function point) = ‖element‖ := by
  have element_integrable : Integrable (element : ℝ → ℝ) volume :=
    memLp_one_iff_integrable.mp (Lp.memLp element)
  let function : ℝ → ℝ := fun point => max (element_integrable.aestronglyMeasurable.mk element point) 0
  have function_measurable : Measurable function :=
    element_integrable.aestronglyMeasurable.stronglyMeasurable_mk.measurable.max measurable_const
  have function_nonnegative : ∀ point, 0 ≤ function point := fun _ => le_max_right _ _
  have function_eq : function =ᵐ[volume] (element : ℝ → ℝ) := by
    filter_upwards [element_integrable.aestronglyMeasurable.ae_eq_mk,
      (Lp.coeFn_nonneg element).mpr positive] with point equality nonnegative
    change (0 : ℝ) ≤ (element : ℝ → ℝ) point at nonnegative
    simp only [function, ← equality, max_eq_left nonnegative]
  have function_integrable := element_integrable.congr function_eq.symm
  have toL1_eq : function_integrable.toL1 function = element := by
    apply Lp.ext
    exact function_integrable.coeFn_toL1.trans function_eq
  refine ⟨function, function_nonnegative, function_measurable, function_integrable, function_eq, ?_⟩
  rw [← toL1_eq, L1.norm_of_fun_eq_integral_norm]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun point => (Real.norm_of_nonneg (function_nonnegative point)).symm)

/-- Actual prefix-local L1 convergence supplies the manuscript one-sided
upper envelope, with actual complete frozen kernels and an everywhere
nonnegative L1 error of the precise geometric-polynomial size. -/
theorem rootSobolevGoodSet_prefix_density_envelope {exponent : ℝ}
    (data : RootFibreData exponent) (orderIndex bound : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∃ minimumDepth : ℕ,
      ∀ (depth : ℕ) (word : Fin depth → Bool × Bool), minimumDepth ≤ depth →
        (goodSetPrefixSelected data orderIndex bound depth word).Nonempty →
        ∃ representative ∈ rootSobolevGoodSet data orderIndex bound,
          (∀ index : Fin depth, representative index = word index) ∧
          ∃ kernel error : ℝ → ℝ,
            (∀ point, 0 ≤ kernel point) ∧ (∀ point, 0 ≤ error point) ∧
            Measurable kernel ∧ Measurable error ∧ Integrable kernel volume ∧ Integrable error volume ∧
            MemLp kernel 2 volume ∧
            completeRootKernelLaw data representative depth =
              volume.withDensity (fun point => ENNReal.ofReal (kernel point)) ∧
            (∀ᵐ point ∂volume, goodSetPrefixDensity data orderIndex bound depth word point ≤
              kernel point + error point) ∧
            (∫ point, error point) ≤ constant * ((depth : ℝ) + 1) ^
              (2 * (1 / ((orderIndex : ℝ) + 1)) / (3 + 2 * (1 / ((orderIndex : ℝ) + 1)))) *
              data.upper ^ ((2 * (1 / ((orderIndex : ℝ) + 1)) /
                (3 + 2 * (1 / ((orderIndex : ℝ) + 1)))) * depth) := by
  obtain ⟨constant, constant_nonnegative, minimumDepth, envelopes⟩ :=
    rootSobolevGoodSet_prefix_L1_envelope data orderIndex bound
  refine ⟨constant, constant_nonnegative, minimumDepth, ?_⟩
  intro depth word depth_ge nonempty
  let selected := goodSetPrefixSelected data orderIndex bound depth word
  let representative := prefixRepresentative selected depth word
  have witness : ∃ digits ∈ selected, ∀ index : Fin depth, digits index = word index := by
    obtain ⟨digits, member⟩ := nonempty
    exact ⟨digits, member, member.2⟩
  have representative_member : representative ∈ selected := prefixRepresentative_mem selected depth word witness
  have kernel_exists := completeRootKernelLaw_hasL2Density data representative depth
    (rootSobolevGoodSet_projected_density data orderIndex bound representative representative_member.1)
  let kernel := measureDensity (completeRootKernelLaw data representative depth) kernel_exists
  have kernel_properties := measureDensity_properties (completeRootKernelLaw data representative depth) kernel_exists
  obtain ⟨errorElement, error_positive, envelope, error_norm⟩ := envelopes depth word depth_ge
  obtain ⟨error, error_nonnegative, error_measurable, error_integrable, error_eq, error_integral⟩ :=
    nonnegative_L1_representative errorElement error_positive
  have initial_eq : selectedWeightedKernelL1 data orderIndex bound selected Set.inter_subset_left
      ((4 : ℝ≥0∞) ^ depth) (by finiteness) depth =
      measureDensityL1 (completeRootKernelLaw data representative depth) kernel_exists := by
    have transport_density (first second : Measure ℝ) (equality : first = second)
        (first_exists : LinearRegularity.HasL2Density first)
        (second_exists : LinearRegularity.HasL2Density second) :
        measureDensityL1 first first_exists = measureDensityL1 second second_exists := by
      cases equality
      rfl
    exact transport_density _ _
      (goodSetPrefixSelected_initial_kernel_law data orderIndex bound depth word nonempty) _ kernel_exists
  rw [initial_eq] at envelope
  refine ⟨representative, representative_member.1,
    fun index => prefixRepresentative_matches selected depth word index,
    kernel, error, kernel_properties.1, error_nonnegative, kernel_properties.2.1,
    error_measurable, kernel_properties.2.2.1, error_integrable, kernel_properties.2.2.2.1,
    kernel_properties.2.2.2.2, ?_, error_integral.trans_le error_norm⟩
  have comparison := (Lp.coeFn_le _ _).mpr envelope
  filter_upwards [comparison, (goodSetPrefixDensity_properties data orderIndex bound depth word).2.2.coeFn_toL1,
    Lp.coeFn_add (measureDensityL1 (completeRootKernelLaw data representative depth) kernel_exists) errorElement,
    kernel_properties.2.2.1.coeFn_toL1, error_eq] with point comparison actual_eq sum_eq kernel_eq error_eq
  rw [actual_eq, sum_eq] at comparison
  change goodSetPrefixDensity data orderIndex bound depth word point ≤
    (measureDensityL1 (completeRootKernelLaw data representative depth) kernel_exists : ℝ → ℝ) point +
      (errorElement : ℝ → ℝ) point at comparison
  unfold measureDensityL1 at comparison
  rw [kernel_eq, ← error_eq] at comparison
  simpa only [kernel] using comparison

/-- The density-tail estimate tolerates the unavoidable null set in an L1
upper envelope. All densities still refer to the actual parameter measure. -/
theorem density_tail_bound_ae (density kernel error : ℝ → ℝ)
    (threshold : ℝ) (threshold_positive : 0 < threshold)
    (density_integrable : Integrable density volume)
    (square_integrable : Integrable (fun point => kernel point ^ 2) volume)
    (error_integrable : Integrable error volume)
    (tail_measurable : MeasurableSet {point | threshold < density point})
    (kernel_nonnegative : ∀ point, 0 ≤ kernel point) (error_nonnegative : ∀ point, 0 ≤ error point)
    (dominated : ∀ᵐ point ∂volume, density point ≤ kernel point + error point) :
    (∫ point in {point | threshold < density point}, density point) ≤
      2 / threshold * (∫ point, kernel point ^ 2) + 3 * (∫ point, error point) := by
  rw [← integral_indicator tail_measurable]
  have majorant_integrable := (square_integrable.const_mul (2 / threshold)).add (error_integrable.const_mul 3)
  calc
    _ ≤ ∫ point, (2 / threshold * kernel point ^ 2 + 3 * error point) := by
      apply integral_mono_ae (density_integrable.indicator tail_measurable) majorant_integrable
      filter_upwards [dominated] with point domination
      change {point | threshold < density point}.indicator density point ≤
        2 / threshold * kernel point ^ 2 + 3 * error point
      by_cases member : threshold < density point
      · rw [Set.indicator_of_mem (s := {point | threshold < density point}) member]
        have bound := tail_pointwise (density point) (kernel point) (error point) threshold threshold_positive
          (kernel_nonnegative point) (error_nonnegative point) domination member
        convert bound using 1 <;> ring
      · rw [Set.indicator_of_notMem (s := {point | threshold < density point}) member]
        exact add_nonneg (mul_nonneg (div_nonneg (by norm_num) threshold_positive.le) (sq_nonneg _))
          (mul_nonneg (by norm_num) (error_nonnegative point))
    _ = _ := by rw [integral_add (square_integrable.const_mul (2 / threshold))
      (error_integrable.const_mul 3), integral_const_mul, integral_const_mul]

/-- The actual support comparison holds for every representative sharing
the chosen prefix, including the representative used by local refinement. -/
theorem goodSetPrefixDensity_threshold_at_representative {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ minimumDepth : ℕ, ∀ (orderIndex bound depth : ℕ), minimumDepth ≤ depth →
      ∀ (word : Fin depth → Bool × Bool) (representative : ℕ → Bool × Bool),
        (∀ index : Fin depth, representative index = word index) → ∀ loss : ℝ,
          ∀ᵐ parameter ∂volume, 0 < goodSetPrefixDensity data orderIndex bound depth word parameter →
            (1 / 2 : ℝ) * data.root representative ^ (-(depth : ℝ)) * Real.exp (loss * depth) ≤
              parameter ^ (-(depth : ℝ)) * Real.exp (loss * depth) := by
  obtain ⟨minimumDepth, thresholds⟩ := rootFibreData_density_thresholds data
  refine ⟨minimumDepth, ?_⟩
  intro orderIndex bound depth depth_ge word representative representative_matches loss
  filter_upwards [goodSetPrefixDensity_actual_range data orderIndex bound depth word]
    with parameter actual_range positive
  obtain ⟨digits, _, prefix_member, root_eq⟩ := actual_range positive
  have agreement : ∀ index < depth, representative index = digits index := by
    intro index before
    exact (representative_matches ⟨index, before⟩).trans (prefix_member ⟨index, before⟩).symm
  simpa only [root_eq] using thresholds representative digits depth depth_ge agreement loss

/-- Constant-threshold domination applies only on the actual positive-density
support; zero density elsewhere makes every bad-event integral vanish there. -/
theorem variable_density_tail_le_constant_tail (density thresholdFunction : ℝ → ℝ) (threshold : ℝ)
    (nonnegative : ∀ point, 0 ≤ density point) (integrable : Integrable density volume)
    (variable_measurable : MeasurableSet {point | thresholdFunction point < density point})
    (constant_measurable : MeasurableSet {point | threshold < density point})
    (support_bound : ∀ᵐ point ∂volume, 0 < density point → threshold ≤ thresholdFunction point) :
    (∫ point in {point | thresholdFunction point < density point}, density point) ≤
      ∫ point in {point | threshold < density point}, density point := by
  rw [← integral_indicator variable_measurable, ← integral_indicator constant_measurable]
  apply integral_mono_ae (integrable.indicator variable_measurable) (integrable.indicator constant_measurable)
  filter_upwards [support_bound] with point support_bound
  by_cases positive : 0 < density point
  · by_cases bad : thresholdFunction point < density point
    · rw [Set.indicator_of_mem (s := {point | thresholdFunction point < density point}) bad,
        Set.indicator_of_mem (s := {point | threshold < density point}) ((support_bound positive).trans_lt bad)]
    · rw [Set.indicator_of_notMem (s := {point | thresholdFunction point < density point}) bad]
      by_cases constant_member : threshold < density point
      · rw [Set.indicator_of_mem (s := {point | threshold < density point}) constant_member]
        exact nonnegative point
      · rw [Set.indicator_of_notMem (s := {point | threshold < density point}) constant_member]
  · have zero : density point = 0 := le_antisymm (le_of_not_gt positive) (nonnegative point)
    simp only [zero, Set.indicator_apply, ite_self, le_refl]

/-- The exact coherent conditional prefix-density tails have a summable
uniform bound. This is the missing actual input to the conditional
Borel--Cantelli theorem, not a premise about independent frozen models. -/
theorem rootSobolevGoodSet_prefix_tails_summable {exponent : ℝ}
    (data : RootFibreData exponent) (orderIndex bound : ℕ) (slack : ℝ) (slack_positive : 0 < slack) :
    Summable (goodSetPrefixTailTotal data orderIndex bound slack) := by
  classical
  obtain ⟨errorConstant, error_nonnegative, envelopeDepth, envelopes⟩ :=
    rootSobolevGoodSet_prefix_density_envelope data orderIndex bound
  obtain ⟨kernelConstant, kernel_nonnegative, square_bounds⟩ :=
    rootSobolevGoodSet_frozen_kernel_square_bound data orderIndex bound
  obtain ⟨thresholdDepth, thresholds⟩ := goodSetPrefixDensity_threshold_at_representative data
  let order : ℝ := 2 * (1 / ((orderIndex : ℝ) + 1)) / (3 + 2 * (1 / ((orderIndex : ℝ) + 1)))
  let errorRate : ℕ → ℝ := fun depth => errorConstant * ((depth : ℝ) + 1) ^ order *
    data.upper ^ (order * depth)
  let majorant : ℕ → ℝ := fun depth =>
    4 * kernelConstant * Real.exp (-(slack * depth)) + 3 * errorRate depth
  have order_bounds := interpolation_exponent_bounds (1 / ((orderIndex : ℝ) + 1)) (by positivity)
  have upper_nonnegative : 0 ≤ data.upper := by linarith [data.lower_gt_quarter, data.ordered]
  have majorant_nonnegative (depth : ℕ) : 0 ≤ majorant depth := by
    dsimp [majorant, errorRate]
    positivity
  have error_summable : Summable errorRate := by
    simpa only [errorRate, mul_assoc] using
      (summable_replacement_rate data.upper order upper_nonnegative (by linarith [data.upper_lt_half])
        order_bounds.1 order_bounds.2).mul_left errorConstant
  have exponential_summable : Summable (fun depth : ℕ => Real.exp (-(slack * depth))) := by
    have geometric := summable_geometric_of_lt_one (Real.exp_pos (-slack)).le
      (by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (neg_lt_zero.mpr slack_positive))
    convert geometric using 1
    funext depth
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have majorant_summable : Summable majorant :=
    (exponential_summable.mul_left (4 * kernelConstant)).add (error_summable.mul_left 3)
  have branch_bound (depth : ℕ) (depth_ge : max envelopeDepth thresholdDepth ≤ depth)
      (word : Fin depth → Bool × Bool) :
      (∫ parameter in goodSetPrefixBadParameters data orderIndex bound depth word slack,
        goodSetPrefixDensity data orderIndex bound depth word parameter) ≤ majorant depth := by
    let density := goodSetPrefixDensity data orderIndex bound depth word
    have density_properties := goodSetPrefixDensity_properties data orderIndex bound depth word
    by_cases nonempty : (goodSetPrefixSelected data orderIndex bound depth word).Nonempty
    · obtain ⟨representative, representative_good, representative_matches,
        kernel, error, kernel_positive, error_positive, kernel_measurable, error_measurable,
        kernel_integrable, error_integrable, kernel_square, kernel_law, envelope, error_integral⟩ :=
        envelopes depth word ((le_max_left _ _).trans depth_ge) nonempty
      obtain ⟨otherKernel, other_positive, other_measurable, other_integrable, other_square,
        other_law, square_bound⟩ := square_bounds representative representative_good depth
      have square_bound_actual : (∫ point, kernel point ^ 2) ≤ kernelConstant / data.root representative ^ depth := by
        have equality := nonnegative_density_unique kernel otherKernel kernel_positive other_positive
          kernel_measurable other_measurable kernel_law other_law
        have integrals : (∫ point, kernel point ^ 2) = ∫ point, otherKernel point ^ 2 :=
          integral_congr_ae (equality.mono (fun _ equal => congrArg (fun value : ℝ => value ^ 2) equal))
        exact integrals.trans_le square_bound
      let threshold : ℝ := (1 / 2 : ℝ) * data.root representative ^ (-(depth : ℝ)) * Real.exp (slack * depth)
      have root_positive : 0 < data.root representative := by
        linarith [data.lower_gt_quarter, (data.root_in_band representative).1]
      have threshold_positive : 0 < threshold := by dsimp [threshold]; positivity
      have support_bound := thresholds orderIndex bound depth ((le_max_right _ _).trans depth_ge)
        word representative representative_matches slack
      have constant_measurable : MeasurableSet {point | threshold < density point} :=
        measurableSet_lt measurable_const density_properties.2.1
      have tail_bound := density_tail_bound_ae density kernel error threshold threshold_positive density_properties.2.2
        ((memLp_two_iff_integrable_sq kernel_measurable.aestronglyMeasurable).mp kernel_square)
        error_integrable constant_measurable kernel_positive error_positive envelope
      have fixed_bound : 2 / threshold * (∫ point, kernel point ^ 2) + 3 * (∫ point, error point) ≤
          majorant depth := by
        calc
          _ ≤ 2 / threshold * (kernelConstant / data.root representative ^ depth) + 3 * errorRate depth :=
            add_le_add (mul_le_mul_of_nonneg_left square_bound_actual (by positivity))
              (mul_le_mul_of_nonneg_left error_integral (by norm_num))
          _ = _ := by
            dsimp [threshold, majorant]
            rw [Real.rpow_neg root_positive.le, Real.rpow_natCast, Real.exp_neg]
            field_simp [(pow_pos root_positive depth).ne', (Real.exp_pos (slack * depth)).ne']
            <;> ring
      exact (variable_density_tail_le_constant_tail density
        (fun parameter => parameter ^ (-(depth : ℝ)) * Real.exp (slack * depth)) threshold
        density_properties.1 density_properties.2.2
        (measurableSet_goodSetPrefixBadParameters data orderIndex bound depth word slack)
        constant_measurable support_bound).trans (tail_bound.trans fixed_bound)
    · have zero : density =ᵐ[volume] 0 := by
        filter_upwards [goodSetPrefixDensity_actual_range data orderIndex bound depth word] with point actual_range
        by_contra not_zero
        have positive : 0 < density point := lt_of_le_of_ne (density_properties.1 point) (Ne.symm not_zero)
        obtain ⟨digits, good, prefix_member, _⟩ := actual_range positive
        exact nonempty ⟨digits, good, prefix_member⟩
      have zero_integral : (∫ parameter in goodSetPrefixBadParameters data orderIndex bound depth word slack,
          density parameter) = 0 := by
        rw [integral_congr_ae (ae_restrict_of_ae zero)]
        simp only [Pi.zero_apply, integral_zero]
      exact zero_integral.trans_le (majorant_nonnegative depth)
  have total_bound (depth : ℕ) (depth_ge : max envelopeDepth thresholdDepth ≤ depth) :
      goodSetPrefixTailTotal data orderIndex bound slack depth ≤ majorant depth := by
    unfold goodSetPrefixTailTotal
    calc
      _ ≤ ∑ _word : Fin depth → Bool × Bool, ((4 : ℝ)⁻¹ ^ depth) * majorant depth := by
        apply Finset.sum_le_sum
        intro word _
        exact mul_le_mul_of_nonneg_left (branch_bound depth depth_ge word) (by positivity)
      _ = majorant depth := by
        rw [← Finset.sum_mul]
        have weights : (∑ _word : Fin depth → Bool × Bool, (4 : ℝ)⁻¹ ^ depth) = 1 := by
          simpa only [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat] using pairedWord_weights_toReal depth
        rw [weights, one_mul]
  apply Summable.of_norm_bounded_eventually_nat majorant_summable
  filter_upwards [Filter.eventually_ge_atTop (max envelopeDepth thresholdDepth)] with depth depth_ge
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact total_bound depth depth_ge
  · unfold goodSetPrefixTailTotal
    exact Finset.sum_nonneg (fun word _ => mul_nonneg (by positivity)
      (setIntegral_nonneg (measurableSet_goodSetPrefixBadParameters data orderIndex bound depth word slack)
        (fun _ _ => (goodSetPrefixDensity_properties data orderIndex bound depth word).1 _)))

end LambdaCantor.First.Roots
