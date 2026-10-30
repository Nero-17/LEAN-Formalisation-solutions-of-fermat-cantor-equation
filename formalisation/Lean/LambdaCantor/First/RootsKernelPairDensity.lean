import LambdaCantor.First.RootsDensityReplacement
import LambdaCantor.First.RootsSupportedDensity
import LambdaCantor.First.RootsExternalFourierDensity
import LambdaCantor.First.RootsKernelPairEnergy

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

/-- A continuous full-address observable with finite weighted characteristic
energy has an actual density supported on any interval containing its range. -/
theorem continuous_paired_law_supported_density
    (coordinate : (ℕ → Bool × Bool) → ℝ) (continuous : Continuous coordinate)
    (radius order : ℝ) (order_nonnegative : 0 ≤ order)
    (range_bound : ∀ digits, |coordinate digits| ≤ radius)
    (finite_energy : (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ order *
      ‖charFun (pairedAddressMeasure.map coordinate) frequency‖ ^ 2)) ≠ ∞) :
    ∃ density : ℝ → ℝ, (∀ point, 0 ≤ density point) ∧ Measurable density ∧
      Integrable density volume ∧ MemLp density 2 volume ∧
      pairedAddressMeasure.map coordinate = volume.withDensity (fun point => ENNReal.ofReal (density point)) ∧
      ∀ point, point ∉ Set.Icc (-radius) radius → density point = 0 := by
  have compact_range : IsCompact (Set.range coordinate) := isCompact_range continuous
  have compact_support : ∃ support : Set ℝ, IsCompact support ∧ (pairedAddressMeasure.map coordinate) supportᶜ = 0 := by
    refine ⟨Set.range coordinate, compact_range, ?_⟩
    rw [Measure.map_apply continuous.measurable compact_range.isClosed.measurableSet.compl]
    have empty_preimage : coordinate ⁻¹' (Set.range coordinate)ᶜ = ∅ := by ext digits; simp
    rw [empty_preimage, measure_empty]
  have concentrated : (pairedAddressMeasure.map coordinate) (Set.Icc (-radius) radius)ᶜ = 0 := by
    rw [Measure.map_apply continuous.measurable measurableSet_Icc.compl]
    have empty_preimage : coordinate ⁻¹' (Set.Icc (-radius) radius)ᶜ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro digits outside
      exact outside (abs_le.mp (range_bound digits))
    rw [empty_preimage, measure_empty]
  exact supportedL2Density_exists
    (hasL2Density_of_weighted_energy _ compact_support order order_nonnegative finite_energy)
    (Set.Icc (-radius) radius) measurableSet_Icc concentrated

/-- Actual parent/child replacement laws have actual supported densities with
one uniform quantitative L1 error. All geometric and energy premises are
derived from concrete root data and membership in the fixed compact good set. -/
theorem rootSobolevGoodSet_actual_density_replacement {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound : ℕ) :
    ∃ prefactor displacementConstant : ℝ, 0 ≤ prefactor ∧ 0 < displacementConstant ∧ ∃ minimumDepth : ℕ,
      ∀ (parent child : ℕ → Bool × Bool) (depth : ℕ), minimumDepth ≤ depth →
        parent ∈ rootSobolevGoodSet data orderIndex bound → child ∈ rootSobolevGoodSet data orderIndex bound →
        (∀ index < depth, parent index = child index) →
        ∃ leftDensity rightDensity : ℝ → ℝ,
          (∀ point, 0 ≤ leftDensity point) ∧ (∀ point, 0 ≤ rightDensity point) ∧
          Measurable leftDensity ∧ Measurable rightDensity ∧
          Integrable leftDensity volume ∧ Integrable rightDensity volume ∧
          pairedAddressMeasure.map (parentFrozenCoordinate data parent child depth) =
            volume.withDensity (fun point => ENNReal.ofReal (leftDensity point)) ∧
          pairedAddressMeasure.map (childFrozenCoordinate data parent child depth) =
            volume.withDensity (fun point => ENNReal.ofReal (rightDensity point)) ∧
          (∫ point : ℝ, |leftDensity point - rightDensity point|) ≤ prefactor *
            (displacementConstant * ((depth : ℝ) + 1) * data.upper ^ depth) ^
              (2 * (1 / ((orderIndex : ℝ) + 1)) / (3 + 2 * (1 / ((orderIndex : ℝ) + 1)))) := by
  obtain ⟨radius, radius_positive, supportDepth, support⟩ := parent_child_frozen_coordinate_support data
  obtain ⟨displacementConstant, displacement_positive, couplingDepth, coupling⟩ := parent_child_frozen_coordinate_coupling data
  obtain ⟨energyConstant, energy_finite, energyDepth, energies⟩ := parent_child_frozen_energy_bound data orderIndex bound
  let order : ℝ := 1 / ((orderIndex : ℝ) + 1)
  have order_positive : 0 < order := by dsimp [order]; positivity
  let interpolationConstant : ℝ := max ((2 / 3 : ℝ) * (2 * Real.pi) ^ 2)
    (4 * (2 : ℝ) ^ order * energyConstant.toReal)
  have interpolation_nonnegative : 0 ≤ interpolationConstant :=
    le_trans (by positivity) (le_max_left _ _)
  letI : IsFiniteMeasure (volume.restrict (Set.Icc (-radius) radius)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
  refine ⟨Real.sqrt (volume.real (Set.Icc (-radius) radius)) * Real.sqrt (2 * interpolationConstant),
    displacementConstant, mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), displacement_positive,
    max supportDepth (max couplingDepth energyDepth), ?_⟩
  intro parent child depth depth_ge parent_good child_good agreement
  have depth_support : supportDepth ≤ depth := (le_max_left _ _).trans depth_ge
  have depth_coupling : couplingDepth ≤ depth := (le_max_left couplingDepth energyDepth).trans ((le_max_right _ _).trans depth_ge)
  have depth_energy : energyDepth ≤ depth := (le_max_right couplingDepth energyDepth).trans ((le_max_right _ _).trans depth_ge)
  have pair_energy := energies parent child depth depth_energy parent_good child_good agreement
  obtain ⟨leftDensity, left_nonnegative, left_measurable, left_integrable, left_square, left_law, left_support⟩ :=
    continuous_paired_law_supported_density _ (continuous_parentFrozenCoordinate data parent child depth)
      radius order order_positive.le (fun tail => (support parent child depth depth_support agreement tail).1)
      (ne_top_of_le_ne_top energy_finite pair_energy.1)
  obtain ⟨rightDensity, right_nonnegative, right_measurable, right_integrable, right_square, right_law, right_support⟩ :=
    continuous_paired_law_supported_density _ (continuous_childFrozenCoordinate data parent child depth)
      radius order order_positive.le (fun tail => (support parent child depth depth_support agreement tail).2)
      (ne_top_of_le_ne_top energy_finite pair_energy.2)
  refine ⟨leftDensity, rightDensity, left_nonnegative, right_nonnegative, left_measurable, right_measurable,
    left_integrable, right_integrable, left_law, right_law, ?_⟩
  apply coupled_supported_density_l1_bound pairedAddressMeasure
    (parentFrozenCoordinate data parent child depth) (childFrozenCoordinate data parent child depth)
    (continuous_parentFrozenCoordinate data parent child depth).measurable
    (continuous_childFrozenCoordinate data parent child depth).measurable
    leftDensity rightDensity left_nonnegative right_nonnegative left_measurable right_measurable
    left_integrable right_integrable left_square right_square left_law right_law
    (Set.Icc (-radius) radius) left_support right_support
    (displacementConstant * ((depth : ℝ) + 1) * data.upper ^ depth) order energyConstant.toReal interpolationConstant
  · have upper_positive : 0 < data.upper := by linarith [data.lower_gt_quarter, data.ordered]
    positivity
  · exact order_positive
  · exact ENNReal.toReal_nonneg
  · exact interpolation_nonnegative
  · exact le_max_left _ _
  · exact le_max_right _ _
  · simpa only [ENNReal.ofReal_toReal energy_finite] using pair_energy.1
  · simpa only [ENNReal.ofReal_toReal energy_finite] using pair_energy.2
  · exact Filter.Eventually.of_forall (fun tail => coupling parent child depth depth_coupling agreement tail)

end LambdaCantor.First.Roots
