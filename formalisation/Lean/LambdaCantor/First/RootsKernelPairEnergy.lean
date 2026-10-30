import LambdaCantor.First.RootsKernelPairModel
import LambdaCantor.First.RootsAffineEnergy
import LambdaCantor.First.RootsGoodSets

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

theorem parent_child_frozen_scale_lower {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ lowerScale : ℝ, 0 < lowerScale ∧ ∃ minimumDepth : ℕ,
      ∀ (parent child : ℕ → Bool × Bool) (depth : ℕ), minimumDepth ≤ depth →
        (∀ index < depth, parent index = child index) →
        lowerScale ≤ |-rootKernelVertical data parent depth * data.root parent / data.root parent ^ depth| ∧
        lowerScale ≤ |-rootKernelVertical data child (depth + 1) / data.root parent ^ depth| := by
  obtain ⟨coefficientLower, coefficientUpper, coefficient_positive, _, coefficient_bounds⟩ :=
    rootKernelVertical_uniform_normalization data
  obtain ⟨minimumDepth, scale_bounds⟩ := rootFibreData_parent_child_scale_ratio data
  have lower_positive : 0 < data.lower := by linarith [data.lower_gt_quarter]
  refine ⟨coefficientLower * (data.lower / 2), by positivity, minimumDepth, ?_⟩
  intro parent child depth depth_ge agreement
  have parent_positive : 0 < data.root parent := lower_positive.trans_le (data.root_in_band parent).1
  have child_positive : 0 < data.root child := lower_positive.trans_le (data.root_in_band child).1
  constructor
  · have identity : -rootKernelVertical data parent depth * data.root parent / data.root parent ^ depth =
        -(rootKernelVertical data parent depth / data.root parent ^ depth) * data.root parent := by ring
    rw [identity, abs_mul, abs_neg, abs_of_pos parent_positive]
    apply mul_le_mul (coefficient_bounds parent depth).1 _ (by positivity) (abs_nonneg _)
    linarith [(data.root_in_band parent).1]
  · have identity : -rootKernelVertical data child (depth + 1) / data.root parent ^ depth =
        -(rootKernelVertical data child (depth + 1) / data.root child ^ (depth + 1)) *
          (data.root child ^ (depth + 1) / data.root parent ^ depth) := by
      field_simp [pow_ne_zero _ child_positive.ne', pow_ne_zero _ parent_positive.ne']
    rw [identity, abs_mul, abs_neg, abs_of_pos (div_pos (pow_pos child_positive _) (pow_pos parent_positive _))]
    exact mul_le_mul (coefficient_bounds child (depth + 1)).1
      (scale_bounds parent child depth depth_ge agreement).1 (by positivity) (abs_nonneg _)

/-- Uniform good-set energy bounds for the two actual laws in a replacement,
including the parent's fixed first digit and the child's different scale. -/
theorem parent_child_frozen_energy_bound {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound : ℕ) :
    ∃ constant : ℝ≥0∞, constant ≠ ∞ ∧ ∃ minimumDepth : ℕ,
      ∀ (parent child : ℕ → Bool × Bool) (depth : ℕ), minimumDepth ≤ depth →
        parent ∈ rootSobolevGoodSet data orderIndex bound →
        child ∈ rootSobolevGoodSet data orderIndex bound →
        (∀ index < depth, parent index = child index) →
        (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ (1 / ((orderIndex : ℝ) + 1)) *
          ‖charFun (pairedAddressMeasure.map (parentFrozenCoordinate data parent child depth)) frequency‖ ^ 2)) ≤ constant ∧
        (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ (1 / ((orderIndex : ℝ) + 1)) *
          ‖charFun (pairedAddressMeasure.map (childFrozenCoordinate data parent child depth)) frequency‖ ^ 2)) ≤ constant := by
  obtain ⟨lowerScale, lower_positive, minimumDepth, scale_bounds⟩ := parent_child_frozen_scale_lower data
  let order : ℝ := 1 / ((orderIndex : ℝ) + 1)
  let multiplier : ℝ≥0∞ := ENNReal.ofReal ((1 + lowerScale⁻¹ ^ 2) ^ order) * ENNReal.ofReal lowerScale⁻¹
  have multiplier_finite : multiplier ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine ⟨multiplier * bound, ENNReal.mul_ne_top multiplier_finite (by simp), minimumDepth, ?_⟩
  intro parent child depth depth_ge parent_good child_good agreement
  have model_measurable (representative : ℕ → Bool × Bool) :
      Measurable (projectedRootModel (rootFibreState data representative)) := by
    have address_measurable := (continuous_address
      (show 0 ≤ data.root representative by linarith [data.lower_gt_quarter, (data.root_in_band representative).1])
      (show data.root representative < 1 by linarith [data.upper_lt_half, (data.root_in_band representative).2])).measurable
    exact (measurable_const.mul (address_measurable.comp (by fun_prop))).add
      (address_measurable.comp (by fun_prop))
  have energy_bound (representative : ℕ → Bool × Bool) (coordinate : (ℕ → Bool × Bool) → ℝ)
      (center scale : ℝ) (scale_lower : lowerScale ≤ |scale|)
      (model : ∀ tail, coordinate tail = center + scale * projectedRootModel (rootFibreState data representative) tail)
      (good : representative ∈ rootSobolevGoodSet data orderIndex bound) :
      (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ order *
        ‖charFun (pairedAddressMeasure.map coordinate) frequency‖ ^ 2)) ≤ multiplier * bound := by
    have law : pairedAddressMeasure.map coordinate =
        (pairedAddressMeasure.map (projectedRootModel (rootFibreState data representative))).map
          (fun value => center + scale * value) := by
      rw [Measure.map_map (by fun_prop) (model_measurable representative)]
      congr 1
      funext tail
      exact model tail
    rw [law]
    exact (affine_characteristic_energy_bound _ center scale lowerScale order lower_positive scale_lower
      (by dsimp [order]; positivity)).trans (mul_le_mul_left' good multiplier)
  obtain ⟨⟨parentCenter, parent_model⟩, ⟨childCenter, child_model⟩⟩ := parent_child_frozen_coordinate_models data parent child depth
  exact ⟨energy_bound parent _ parentCenter _ (scale_bounds parent child depth depth_ge agreement).1 parent_model parent_good,
    energy_bound child _ childCenter _ (scale_bounds parent child depth depth_ge agreement).2 child_model child_good⟩

end LambdaCantor.First.Roots
