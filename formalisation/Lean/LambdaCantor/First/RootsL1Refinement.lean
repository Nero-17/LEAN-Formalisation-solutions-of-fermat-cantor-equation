import LambdaCantor.First.RootsPairUnnormalize
import LambdaCantor.First.RootsL1FiniteReplacement
import LambdaCantor.First.RootsRetainedKernelSum
import LambdaCantor.First.RootsGoodSetDensities
import LambdaCantor.First.RootsL1Order
import LambdaCantor.First.RootsKernelDeletion
import LambdaCantor.First.RootsActualRate
import Mathlib.Tactic.Choose

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace LambdaCantor.First.Roots

/-- Actual finite kernel law at the compact energy sublevel. -/
def goodSetKernelLaw {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound depth : ℕ) : Measure ℝ :=
  (pairedAddressMeasure.restrict
    (prefixNeighborhood (rootSobolevGoodSet data orderIndex bound) depth)).map
    (selectedRootKernel data (rootSobolevGoodSet data orderIndex bound) depth)

def goodSetKernelDensityL1 {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound depth : ℕ) : Lp ℝ 1 (volume : Measure ℝ) :=
  measureDensityL1 (goodSetKernelLaw data orderIndex bound depth)
    (rootSobolevGoodSet_kernel_sum_density data orderIndex bound depth)

/-- The finite-word weights retain total mass one before deletion. -/
theorem pairedWord_weights_toReal (depth : ℕ) :
    (∑ _word : Fin depth → Bool × Bool, (((4 : ℝ≥0∞)⁻¹ ^ depth).toReal)) = 1 := by
  have cardinality : Fintype.card (Fin depth → Bool × Bool) = 4 ^ depth := by simp
  simp only [Finset.sum_const, Finset.card_univ, cardinality, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

/-- Exact common-child-word refinement converts the actual normalized pair
estimate into a bound for the surviving parent sum and the child sum. -/
theorem rootSobolevGoodSet_retained_L1_replacement
    {exponent : ℝ} (data : RootFibreData exponent) (orderIndex bound : ℕ) :
    ∃ prefactor displacementConstant : ℝ, 0 ≤ prefactor ∧ 0 < displacementConstant ∧
      ∃ minimumDepth : ℕ, ∀ depth, minimumDepth ≤ depth →
        ∃ retained_exists : LinearRegularity.HasL2Density
          ((pairedAddressMeasure.restrict
            (prefixNeighborhood (rootSobolevGoodSet data orderIndex bound) (depth + 1))).map
            (selectedRootKernel data (rootSobolevGoodSet data orderIndex bound) depth)),
          ‖goodSetKernelDensityL1 data orderIndex bound (depth + 1) -
            measureDensityL1 _ retained_exists‖ ≤ prefactor *
            (displacementConstant * ((depth : ℝ) + 1) * data.upper ^ depth) ^
              (2 * (1 / ((orderIndex : ℝ) + 1)) / (3 + 2 * (1 / ((orderIndex : ℝ) + 1)))) := by
  classical
  obtain ⟨prefactor, displacementConstant, prefactor_nonnegative, displacement_positive,
    minimumDepth, pair_bound⟩ := rootSobolevGoodSet_parameter_L1_replacement data orderIndex bound
  refine ⟨prefactor, displacementConstant, prefactor_nonnegative, displacement_positive, minimumDepth, ?_⟩
  intro depth depth_ge
  have upper_positive : 0 < data.upper := by linarith [data.lower_gt_quarter, data.ordered]
  let selected := rootSobolevGoodSet data orderIndex bound
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
        (prefixRepresentative selected (depth + 1) word) depth depth_ge parent_good child_good agreement
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
    (fun word => ((4 : ℝ≥0∞)⁻¹ ^ (depth + 1)) • parentLaw word)
    (fun word _ => hasL2Density_smul (parent_exists word) _ (by finiteness))
  let child_sum_exists := hasL2Density_finset_sum Finset.univ
    (fun word => ((4 : ℝ≥0∞)⁻¹ ^ (depth + 1)) • childLaw word)
    (fun word _ => hasL2Density_smul (child_exists word) _ (by finiteness))
  have parent_sum : (∑ word, ((4 : ℝ≥0∞)⁻¹ ^ (depth + 1)) • parentLaw word) =
      (pairedAddressMeasure.restrict (prefixNeighborhood selected (depth + 1))).map
        (selectedRootKernel data selected depth) := by
    rw [retainedRootKernel_law_eq_sum]
    apply Finset.sum_congr rfl
    intro word _
    by_cases member : admissible word
    · simp only [admissible, selected] at member
      simp only [parentLaw, admissible, selected, if_pos member]
    · simp only [admissible, selected] at member
      simp only [parentLaw, admissible, selected, if_neg member, smul_zero]
  have child_sum : (∑ word, ((4 : ℝ≥0∞)⁻¹ ^ (depth + 1)) • childLaw word) =
      goodSetKernelLaw data orderIndex bound (depth + 1) := by
    unfold goodSetKernelLaw
    rw [selectedRootKernel_law_eq_sum]
    apply Finset.sum_congr rfl
    intro word _
    by_cases member : admissible word
    · simp only [admissible, selected] at member
      simp only [childLaw, admissible, selected, if_pos member]
    · simp only [admissible, selected] at member
      simp only [childLaw, admissible, selected, if_neg member, smul_zero]
  have retained_exists : LinearRegularity.HasL2Density
      ((pairedAddressMeasure.restrict (prefixNeighborhood selected (depth + 1))).map
        (selectedRootKernel data selected depth)) := parent_sum ▸ parent_sum_exists
  have transport_density (first second : Measure ℝ) (equality : first = second)
      (first_exists : LinearRegularity.HasL2Density first)
      (second_exists : LinearRegularity.HasL2Density second) :
      measureDensityL1 first first_exists = measureDensityL1 second second_exists := by
    cases equality
    rfl
  have parent_density := transport_density _ _ parent_sum parent_sum_exists retained_exists
  have child_density := transport_density _ _ child_sum child_sum_exists
    (rootSobolevGoodSet_kernel_sum_density data orderIndex bound (depth + 1))
  refine ⟨retained_exists, ?_⟩
  have estimate := finite_density_replacement_bound Finset.univ parentLaw childLaw parent_exists child_exists
    (fun _ => (4 : ℝ≥0∞)⁻¹ ^ (depth + 1)) (fun _ => by finiteness) _
    (fun word _ => estimates word)
  rw [pairedWord_weights_toReal, one_mul] at estimate
  rw [parent_density, child_density] at estimate
  simpa only [goodSetKernelDensityL1, norm_sub_rev] using estimate

end LambdaCantor.First.Roots
