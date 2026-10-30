import LambdaCantor.First.RootsKernelSupport

noncomputable section
namespace LambdaCantor.First.Roots

/-- Consecutive-depth child scales stay uniformly comparable to the parent
scale, in both directions, for actual roots with a common depth prefix. -/
theorem rootFibreData_parent_child_scale_ratio {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ minimumDepth : ℕ, ∀ (parent child : ℕ → Bool × Bool) (depth : ℕ), minimumDepth ≤ depth →
      (∀ index < depth, parent index = child index) →
      data.lower / 2 ≤ data.root child ^ (depth + 1) / data.root parent ^ depth ∧
      data.root child ^ (depth + 1) / data.root parent ^ depth ≤ 2 * data.upper := by
  obtain ⟨minimumDepth, comparable⟩ := rootFibreData_uniform_scales data
  refine ⟨minimumDepth, ?_⟩
  intro parent child depth depth_ge agreement
  have parent_positive : 0 < data.root parent := by
    linarith [data.lower_gt_quarter, (data.root_in_band parent).1]
  have child_positive : 0 < data.root child := by
    linarith [data.lower_gt_quarter, (data.root_in_band child).1]
  have upper_nonnegative : 0 ≤ data.upper := child_positive.le.trans (data.root_in_band child).2
  have upper := comparable parent child depth depth_ge agreement
  have lower := comparable child parent depth depth_ge (fun index before => (agreement index before).symm)
  rw [pow_succ]
  constructor
  · apply (le_div_iff₀ (pow_pos parent_positive depth)).mpr
    have first := mul_le_mul_of_nonneg_right lower (show 0 ≤ data.lower / 2 by linarith [data.lower_gt_quarter])
    have second := mul_le_mul_of_nonneg_left (data.root_in_band child).1 (pow_pos child_positive depth).le
    nlinarith
  · apply (div_le_iff₀ (pow_pos parent_positive depth)).mpr
    have first := mul_le_mul_of_nonneg_right upper child_positive.le
    have second := mul_le_mul_of_nonneg_left (data.root_in_band child).2
      (show 0 ≤ 2 * data.root parent ^ depth by positivity)
    nlinarith

/-- Parent and child kernels, both normalized about the parent root, have one
common bounded support. Every fresh child tail remains unrestricted. -/
theorem parent_child_kernel_common_support {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ minimumDepth : ℕ,
      ∀ (parent child tail : ℕ → Bool × Bool) (depth : ℕ), minimumDepth ≤ depth →
        (∀ index < depth, parent index = child index) →
        |(completeRootKernel data child (depth + 1) tail - data.root parent) /
          data.root parent ^ depth| ≤ radius := by
  obtain ⟨kernelRadius, radius_positive, support⟩ := completeRootKernel_uniform_support data
  obtain ⟨scaleDepth, scale_bounds⟩ := rootFibreData_parent_child_scale_ratio data
  obtain ⟨rootDepth, root_bound⟩ := rootFibreData_root_displacement data
  have upper_positive : 0 < data.upper := by linarith [data.lower_gt_quarter, data.ordered]
  have root_constant_positive : 0 < 4 * exponent / data.derivative_lower_bound := by
    apply div_pos _ data.derivative_lower_bound_positive
    linarith [data.exponent_gt_one]
  refine ⟨kernelRadius * (2 * data.upper) + 4 * exponent / data.derivative_lower_bound,
    add_pos (mul_pos radius_positive (by positivity)) root_constant_positive,
    max scaleDepth rootDepth, ?_⟩
  intro parent child tail depth depth_ge agreement
  have parent_positive : 0 < data.root parent := by
    linarith [data.lower_gt_quarter, (data.root_in_band parent).1]
  have child_positive : 0 < data.root child := by
    linarith [data.lower_gt_quarter, (data.root_in_band child).1]
  have root_distance := root_bound child parent depth ((le_max_right _ _).trans depth_ge)
    (fun index before => (agreement index before).symm)
  have root_normalized : |(data.root child - data.root parent) / data.root parent ^ depth| ≤
      4 * exponent / data.derivative_lower_bound := by
    rw [abs_div, abs_of_pos (pow_pos parent_positive depth)]
    apply (div_le_iff₀ (pow_pos parent_positive depth)).mpr
    simpa only [abs_sub_comm] using root_distance
  have normalized_kernel : |(completeRootKernel data child (depth + 1) tail - data.root child) /
      data.root parent ^ depth| ≤ kernelRadius * (2 * data.upper) := by
    have identity : (completeRootKernel data child (depth + 1) tail - data.root child) /
        data.root parent ^ depth =
        ((completeRootKernel data child (depth + 1) tail - data.root child) / data.root child ^ (depth + 1)) *
          (data.root child ^ (depth + 1) / data.root parent ^ depth) := by
      field_simp [pow_ne_zero _ parent_positive.ne', pow_ne_zero _ child_positive.ne']
    rw [identity, abs_mul, abs_of_pos (div_pos (pow_pos child_positive _) (pow_pos parent_positive _))]
    exact mul_le_mul (support child tail (depth + 1))
      (scale_bounds parent child depth ((le_max_left _ _).trans depth_ge) agreement).2
      (div_pos (pow_pos child_positive _) (pow_pos parent_positive _)).le radius_positive.le
  have identity : (completeRootKernel data child (depth + 1) tail - data.root parent) /
      data.root parent ^ depth =
      (completeRootKernel data child (depth + 1) tail - data.root child) / data.root parent ^ depth +
      (data.root child - data.root parent) / data.root parent ^ depth := by ring
  rw [identity]
  exact (abs_add_le _ _).trans (add_le_add normalized_kernel root_normalized)

end LambdaCantor.First.Roots
