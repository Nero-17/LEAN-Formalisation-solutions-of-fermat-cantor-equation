import LambdaCantor.First.RootsKernelPairDensity
import LambdaCantor.First.RootsL1Densities

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

theorem continuous_paired_law_hasL2Density (coordinate : (ℕ → Bool × Bool) → ℝ)
    (continuous : Continuous coordinate) (order : ℝ) (order_nonnegative : 0 ≤ order)
    (finite_energy : (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ order *
      ‖charFun (pairedAddressMeasure.map coordinate) frequency‖ ^ 2)) ≠ ∞) :
    LinearRegularity.HasL2Density (pairedAddressMeasure.map coordinate) := by
  apply hasL2Density_of_weighted_energy _ _ order order_nonnegative finite_energy
  refine ⟨Set.range coordinate, isCompact_range continuous, ?_⟩
  rw [Measure.map_apply continuous.measurable (isCompact_range continuous).isClosed.measurableSet.compl]
  have empty_preimage : coordinate ⁻¹' (Set.range coordinate)ᶜ = ∅ := by ext digits; simp
  rw [empty_preimage, measure_empty]

/-- The actual normalized replacement estimate holds for the canonical L1
elements, so it can be summed without reconciling pointwise density versions. -/
theorem rootSobolevGoodSet_actual_L1_replacement {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound : ℕ) :
    ∃ prefactor displacementConstant : ℝ, 0 ≤ prefactor ∧ 0 < displacementConstant ∧ ∃ minimumDepth : ℕ,
      ∀ (parent child : ℕ → Bool × Bool) (depth : ℕ), minimumDepth ≤ depth →
        parent ∈ rootSobolevGoodSet data orderIndex bound → child ∈ rootSobolevGoodSet data orderIndex bound →
        (∀ index < depth, parent index = child index) →
        ∃ (left_exists : LinearRegularity.HasL2Density
          (pairedAddressMeasure.map (parentFrozenCoordinate data parent child depth)))
          (right_exists : LinearRegularity.HasL2Density
          (pairedAddressMeasure.map (childFrozenCoordinate data parent child depth))),
          ‖measureDensityL1 _ left_exists - measureDensityL1 _ right_exists‖ ≤ prefactor *
            (displacementConstant * ((depth : ℝ) + 1) * data.upper ^ depth) ^
              (2 * (1 / ((orderIndex : ℝ) + 1)) / (3 + 2 * (1 / ((orderIndex : ℝ) + 1)))) := by
  obtain ⟨prefactor, displacementConstant, prefactor_nonnegative, displacement_positive,
    replacementDepth, replacements⟩ := rootSobolevGoodSet_actual_density_replacement data orderIndex bound
  obtain ⟨energyConstant, energy_finite, energyDepth, energies⟩ :=
    parent_child_frozen_energy_bound data orderIndex bound
  refine ⟨prefactor, displacementConstant, prefactor_nonnegative, displacement_positive,
    max replacementDepth energyDepth, ?_⟩
  intro parent child depth depth_ge parent_good child_good agreement
  have pair_energy := energies parent child depth ((le_max_right _ _).trans depth_ge)
    parent_good child_good agreement
  have left_exists := continuous_paired_law_hasL2Density _
    (continuous_parentFrozenCoordinate data parent child depth)
    (1 / ((orderIndex : ℝ) + 1)) (by positivity)
    (ne_top_of_le_ne_top energy_finite pair_energy.1)
  have right_exists := continuous_paired_law_hasL2Density _
    (continuous_childFrozenCoordinate data parent child depth)
    (1 / ((orderIndex : ℝ) + 1)) (by positivity)
    (ne_top_of_le_ne_top energy_finite pair_energy.2)
  obtain ⟨leftDensity, rightDensity, left_nonnegative, right_nonnegative, left_measurable,
    right_measurable, left_integrable, right_integrable, left_law, right_law, estimate⟩ :=
    replacements parent child depth ((le_max_left _ _).trans depth_ge) parent_good child_good agreement
  refine ⟨left_exists, right_exists, ?_⟩
  rw [measureDensityL1_distance left_exists right_exists leftDensity rightDensity
    left_nonnegative right_nonnegative left_measurable right_measurable
    left_integrable right_integrable left_law right_law]
  exact estimate

end LambdaCantor.First.Roots
