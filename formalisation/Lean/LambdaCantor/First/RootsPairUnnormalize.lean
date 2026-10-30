import LambdaCantor.First.RootsPairL1
import LambdaCantor.First.RootsL1AffineDistance

noncomputable section
open MeasureTheory
namespace LambdaCantor.First.Roots

theorem parentFrozenCoordinate_unnormalize {exponent : ℝ} (data : RootFibreData exponent)
    (parent child : ℕ → Bool × Bool) (depth : ℕ) :
    (pairedAddressMeasure.map (parentFrozenCoordinate data parent child depth)).map
      (fun point => data.root parent + data.root parent ^ depth * point) =
      pairedAddressMeasure.map (fun tail => completeRootKernel data parent depth
        (prependPairedDigit (child depth) tail)) := by
  rw [Measure.map_map (by fun_prop) (continuous_parentFrozenCoordinate data parent child depth).measurable]
  congr 1
  funext tail
  have positive : 0 < data.root parent := by linarith [data.lower_gt_quarter, (data.root_in_band parent).1]
  dsimp [Function.comp_def, parentFrozenCoordinate]
  field_simp [pow_ne_zero depth positive.ne']
  <;> ring

theorem childFrozenCoordinate_unnormalize {exponent : ℝ} (data : RootFibreData exponent)
    (parent child : ℕ → Bool × Bool) (depth : ℕ) :
    (pairedAddressMeasure.map (childFrozenCoordinate data parent child depth)).map
      (fun point => data.root parent + data.root parent ^ depth * point) =
      completeRootKernelLaw data child (depth + 1) := by
  rw [Measure.map_map (by fun_prop) (continuous_childFrozenCoordinate data parent child depth).measurable]
  unfold completeRootKernelLaw
  congr 1
  funext tail
  have positive : 0 < data.root parent := by linarith [data.lower_gt_quarter, (data.root_in_band parent).1]
  dsimp [Function.comp_def, childFrozenCoordinate]
  field_simp [pow_ne_zero depth positive.ne']
  <;> ring

theorem rootSobolevGoodSet_parameter_L1_replacement {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound : ℕ) :
    ∃ prefactor displacementConstant : ℝ, 0 ≤ prefactor ∧ 0 < displacementConstant ∧ ∃ minimumDepth : ℕ,
      ∀ (parent child : ℕ → Bool × Bool) (depth : ℕ), minimumDepth ≤ depth →
        parent ∈ rootSobolevGoodSet data orderIndex bound → child ∈ rootSobolevGoodSet data orderIndex bound →
        (∀ index < depth, parent index = child index) →
        ∃ (left_exists : LinearRegularity.HasL2Density
          (pairedAddressMeasure.map (fun tail => completeRootKernel data parent depth
            (prependPairedDigit (child depth) tail))))
          (right_exists : LinearRegularity.HasL2Density (completeRootKernelLaw data child (depth + 1))),
          ‖measureDensityL1 _ left_exists - measureDensityL1 _ right_exists‖ ≤ prefactor *
            (displacementConstant * ((depth : ℝ) + 1) * data.upper ^ depth) ^
              (2 * (1 / ((orderIndex : ℝ) + 1)) / (3 + 2 * (1 / ((orderIndex : ℝ) + 1)))) := by
  obtain ⟨prefactor, displacementConstant, prefactor_nonnegative, displacement_positive,
    minimumDepth, replacements⟩ := rootSobolevGoodSet_actual_L1_replacement data orderIndex bound
  refine ⟨prefactor, displacementConstant, prefactor_nonnegative, displacement_positive, minimumDepth, ?_⟩
  intro parent child depth depth_ge parent_good child_good agreement
  obtain ⟨left_exists, right_exists, estimate⟩ :=
    replacements parent child depth depth_ge parent_good child_good agreement
  have positive : 0 < data.root parent := by linarith [data.lower_gt_quarter, (data.root_in_band parent).1]
  have left_actual := hasL2Density_affine left_exists (data.root parent) (data.root parent ^ depth)
    (pow_ne_zero depth positive.ne')
  have right_actual := hasL2Density_affine right_exists (data.root parent) (data.root parent ^ depth)
    (pow_ne_zero depth positive.ne')
  rw [parentFrozenCoordinate_unnormalize] at left_actual
  rw [childFrozenCoordinate_unnormalize] at right_actual
  refine ⟨left_actual, right_actual, ?_⟩
  have transported := (measureDensityL1_affine_distance left_exists right_exists
    (data.root parent) (data.root parent ^ depth) (pow_ne_zero depth positive.ne')).le.trans estimate
  simpa only [parentFrozenCoordinate_unnormalize, childFrozenCoordinate_unnormalize] using transported

end LambdaCantor.First.Roots
