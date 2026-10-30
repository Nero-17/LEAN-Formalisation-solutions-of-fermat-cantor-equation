import LambdaCantor.First.RootsUniformScales

noncomputable section
namespace LambdaCantor.First.Roots

/-- The inverse level scale at an exponentially close parameter is at least
half the scale at the representative, uniformly at all sufficiently large depths. -/
theorem inverse_level_scale_of_exponential_closeness {lower upper constant : ℝ}
    (lower_positive : 0 < lower) (upper_nonnegative : 0 ≤ upper) (upper_lt_one : upper < 1) :
    ∃ minimumDepth : ℕ, ∀ depth : ℕ, minimumDepth ≤ depth →
      ∀ representative parameter : ℝ, lower ≤ representative → lower ≤ parameter →
        |parameter - representative| ≤ constant * upper ^ depth →
        (1 / 2 : ℝ) * representative ^ (-(depth : ℝ)) ≤ parameter ^ (-(depth : ℝ)) := by
  obtain ⟨minimumDepth, scales⟩ :=
    uniform_scale_ratio_of_exponential_closeness (constant := constant)
      lower_positive upper_nonnegative upper_lt_one
  refine ⟨minimumDepth, ?_⟩
  intro depth depth_ge representative parameter representative_lower parameter_lower close
  have representative_positive := lower_positive.trans_le representative_lower
  have parameter_positive := lower_positive.trans_le parameter_lower
  have inverse_bound := inv_anti₀ (pow_pos parameter_positive depth)
    (scales depth depth_ge representative parameter representative_lower parameter_lower close)
  rw [Real.rpow_neg representative_positive.le, Real.rpow_natCast,
    Real.rpow_neg parameter_positive.le, Real.rpow_natCast]
  simpa only [mul_inv_rev, one_div, mul_comm] using inverse_bound

/-- Actual roots with the same paired prefix satisfy the threshold comparison
needed for the variable-parameter density-tail event. -/
theorem rootFibreData_inverse_level_scales {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ minimumDepth : ℕ, ∀ (representative digits : ℕ → Bool × Bool) (depth : ℕ),
      minimumDepth ≤ depth → (∀ index < depth, representative index = digits index) →
      (1 / 2 : ℝ) * data.root representative ^ (-(depth : ℝ)) ≤
        data.root digits ^ (-(depth : ℝ)) := by
  obtain ⟨minimumDepth, scales⟩ := rootFibreData_uniform_scales data
  refine ⟨minimumDepth, ?_⟩
  intro representative digits depth depth_ge agreement
  have representative_positive : 0 < data.root representative := by
    linarith [data.lower_gt_quarter, (data.root_in_band representative).1]
  have parameter_positive : 0 < data.root digits := by
    linarith [data.lower_gt_quarter, (data.root_in_band digits).1]
  have inverse_bound := inv_anti₀ (pow_pos parameter_positive depth)
    (scales representative digits depth depth_ge agreement)
  rw [Real.rpow_neg representative_positive.le, Real.rpow_natCast,
    Real.rpow_neg parameter_positive.le, Real.rpow_natCast]
  simpa only [mul_inv_rev, one_div, mul_comm] using inverse_bound

/-- Multiplication by the exponential loss factor preserves the uniform
threshold comparison, including at loss zero. -/
theorem rootFibreData_density_thresholds {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ minimumDepth : ℕ, ∀ (representative digits : ℕ → Bool × Bool) (depth : ℕ),
      minimumDepth ≤ depth → (∀ index < depth, representative index = digits index) →
      ∀ loss : ℝ,
        (1 / 2 : ℝ) * data.root representative ^ (-(depth : ℝ)) *
          Real.exp (loss * depth) ≤ data.root digits ^ (-(depth : ℝ)) *
            Real.exp (loss * depth) := by
  obtain ⟨minimumDepth, inverse_scales⟩ := rootFibreData_inverse_level_scales data
  refine ⟨minimumDepth, ?_⟩
  intro representative digits depth depth_ge agreement loss
  exact mul_le_mul_of_nonneg_right
    (inverse_scales representative digits depth depth_ge agreement) (Real.exp_pos _).le

end LambdaCantor.First.Roots
