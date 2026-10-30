import LambdaCantor.First.RootsKernelApproximation
import LambdaCantor.First.RootsUniformScales

noncomputable section
namespace LambdaCantor.First.Roots

/-- Uniform normalized parent-child coupling for the actual frozen root
kernels. The same unrestricted complete address supplies both fresh tails.
The parent expression is evaluated on the selected child cylinder, exactly
as in the four-way first-digit decomposition. -/
theorem rootFibreData_parent_child_kernel_coupling {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∃ minimumDepth : ℕ,
      ∀ (parent child digits : ℕ → Bool × Bool) (depth : ℕ), minimumDepth ≤ depth →
        (∀ index < depth, parent index = child index) →
        (∀ index < depth + 1, child index = digits index) →
        |rootKernelValue data parent digits depth - rootKernelValue data child digits (depth + 1)| /
            data.root parent ^ depth ≤ constant * ((depth : ℝ) + 1) * data.upper ^ depth := by
  obtain ⟨constant, constant_nonnegative, approximationDepth, approximation⟩ :=
    rootFibreData_kernel_approximates_root data
  obtain ⟨scaleDepth, scales⟩ := rootFibreData_uniform_scales data
  have lower_positive : 0 < data.lower := by linarith [data.lower_gt_quarter]
  have lower_lt_one : data.lower < 1 := by linarith [data.ordered, data.upper_lt_half]
  refine ⟨9 * constant / data.lower, div_nonneg (by positivity) lower_positive.le,
    max 1 (max approximationDepth scaleDepth), ?_⟩
  intro parent child digits depth depth_ge parent_child child_digits
  have depth_positive : 1 ≤ depth := (le_max_left _ _).trans depth_ge
  have approximation_ge : approximationDepth ≤ depth :=
    (le_max_left _ _).trans ((le_max_right _ _).trans depth_ge)
  have scale_ge : scaleDepth ≤ depth :=
    (le_max_right _ _).trans ((le_max_right _ _).trans depth_ge)
  have parent_digits : ∀ index < depth, parent index = digits index := by
    intro index index_lt
    exact (parent_child index index_lt).trans (child_digits index (by omega))
  have parent_approximation := approximation parent digits depth approximation_ge parent_digits
  have child_approximation := approximation child digits (depth + 1) (by omega) child_digits
  have parent_positive : 0 < data.root parent := lower_positive.trans_le (data.root_in_band parent).1
  have child_positive : 0 < data.root child := lower_positive.trans_le (data.root_in_band child).1
  have child_lt_one : data.root child < 1 := by linarith [data.upper_lt_half, (data.root_in_band child).2]
  have scale_bound := scales parent child depth scale_ge parent_child
  have scale_squared := (sq_le_sq₀ (pow_nonneg child_positive.le depth)
    (mul_nonneg (by norm_num) (pow_nonneg parent_positive.le depth))).mpr scale_bound
  have child_power_bound : data.root child ^ (2 * (depth + 1) - 1) ≤
      4 * (data.root parent ^ depth) ^ 2 := by
    have exponent_identity : 2 * (depth + 1) - 1 = depth + depth + 1 := by omega
    rw [exponent_identity, pow_succ, pow_add]
    have multiply := mul_le_mul_of_nonneg_left child_lt_one.le
      (mul_nonneg (pow_nonneg child_positive.le depth) (pow_nonneg child_positive.le depth))
    nlinarith [scale_squared, multiply]
  have child_error_bound : |data.root digits - rootKernelValue data child digits (depth + 1)| ≤
      4 * constant * ((depth : ℝ) + 2) * (data.root parent ^ depth) ^ 2 := by
    have bound := mul_le_mul_of_nonneg_left child_power_bound
      (mul_nonneg constant_nonnegative (by positivity : 0 ≤ ((depth + 1 : ℕ) : ℝ) + 1))
    have result := child_approximation.trans bound
    simp only [Nat.cast_add, Nat.cast_one] at result
    nlinarith [result]
  have parent_power_identity : data.root parent ^ (2 * depth - 1) * data.root parent =
      (data.root parent ^ depth) ^ 2 := by
    rw [← pow_succ, show 2 * depth - 1 + 1 = depth * 2 by omega, pow_mul]
  have parent_scaled := mul_le_mul_of_nonneg_right parent_approximation parent_positive.le
  have parent_lower := mul_le_mul_of_nonneg_left (data.root_in_band parent).1
    (abs_nonneg (data.root digits - rootKernelValue data parent digits depth))
  have parent_error_bound : |data.root digits - rootKernelValue data parent digits depth| * data.lower ≤
      constant * ((depth : ℝ) + 1) * (data.root parent ^ depth) ^ 2 := by
    have bound := parent_lower.trans parent_scaled
    rw [mul_assoc (constant * ((depth : ℝ) + 1)), parent_power_identity] at bound
    exact bound
  have child_scaled := mul_le_mul_of_nonneg_right child_error_bound lower_positive.le
  have child_lower_bound : |data.root digits - rootKernelValue data child digits (depth + 1)| * data.lower ≤
      8 * constant * ((depth : ℝ) + 1) * (data.root parent ^ depth) ^ 2 := by
    have coeff_bound : ((depth : ℝ) + 2) * data.lower ≤ 2 * ((depth : ℝ) + 1) := by
      have scaled := mul_le_mul_of_nonneg_left lower_lt_one.le
        (show 0 ≤ (depth : ℝ) + 2 by positivity)
      linarith [Nat.cast_nonneg (α := ℝ) depth]
    have bound : (4 * constant * (data.root parent ^ depth) ^ 2) * (((depth : ℝ) + 2) * data.lower) ≤
        (4 * constant * (data.root parent ^ depth) ^ 2) * (2 * ((depth : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left coeff_bound
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) constant_nonnegative)
          (sq_nonneg (data.root parent ^ depth)))
    nlinarith [child_scaled, bound]
  have triangle := abs_sub_le (rootKernelValue data parent digits depth) (data.root digits)
    (rootKernelValue data child digits (depth + 1))
  rw [abs_sub_comm (rootKernelValue data parent digits depth) (data.root digits)] at triangle
  have scaled_triangle := mul_le_mul_of_nonneg_right triangle lower_positive.le
  have total_bound : |rootKernelValue data parent digits depth - rootKernelValue data child digits (depth + 1)| * data.lower ≤
      9 * constant * ((depth : ℝ) + 1) * (data.root parent ^ depth) ^ 2 := by
    nlinarith [scaled_triangle, parent_error_bound, child_lower_bound]
  have normalized_bound : |rootKernelValue data parent digits depth - rootKernelValue data child digits (depth + 1)| /
      data.root parent ^ depth ≤ (9 * constant / data.lower) * ((depth : ℝ) + 1) * data.root parent ^ depth := by
    apply (div_le_iff₀ (pow_pos parent_positive depth)).mpr
    have identity : (9 * constant / data.lower) * ((depth : ℝ) + 1) * data.root parent ^ depth *
        data.root parent ^ depth = (9 * constant * ((depth : ℝ) + 1) * (data.root parent ^ depth) ^ 2) / data.lower := by ring
    rw [identity]
    exact (le_div_iff₀ lower_positive).mpr total_bound
  exact normalized_bound.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ parent_positive.le (data.root_in_band parent).2 depth)
    (mul_nonneg (div_nonneg (by positivity) lower_positive.le) (by positivity)))

end LambdaCantor.First.Roots
