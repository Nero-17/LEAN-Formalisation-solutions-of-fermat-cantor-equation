import LambdaCantor.First.RootsKernelTails
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open Filter Topology MeasureTheory
namespace LambdaCantor.First.Roots

/-- Every actual prefix-frozen kernel converges to the actual root, uniformly
in its unrestricted address and in the choice of a matching representative. -/
theorem rootFibreData_kernel_uniform_error {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (𝓝 0) ∧
      ∀ᶠ depth in atTop, ∀ representative digits : ℕ → Bool × Bool,
        (∀ index < depth, representative index = digits index) →
        |rootKernelValue data representative digits depth - data.root digits| ≤ error depth := by
  obtain ⟨constant, constant_nonnegative, minimumDepth, approximation⟩ := rootFibreData_kernel_approximates_root data
  have upper_nonnegative : 0 ≤ data.upper := by linarith [data.lower_gt_quarter, data.ordered]
  have upper_lt_one : data.upper < 1 := by linarith [data.upper_lt_half]
  refine ⟨fun depth => constant * (((depth : ℝ) + 1) * data.upper ^ depth), ?_, ?_⟩
  · have linear := tendsto_self_mul_const_pow_of_lt_one upper_nonnegative upper_lt_one
    have geometric := tendsto_pow_atTop_nhds_zero_of_lt_one upper_nonnegative upper_lt_one
    simpa only [add_mul, one_mul, zero_add, mul_zero] using (linear.add geometric).const_mul constant
  · filter_upwards [eventually_ge_atTop (max 1 minimumDepth)] with depth depth_ge
    intro representative digits agreement
    have bound := approximation representative digits depth
      ((le_max_right _ _).trans depth_ge) agreement
    have ratio_nonnegative : 0 ≤ data.root representative := by
      linarith [data.lower_gt_quarter, (data.root_in_band representative).1]
    have powers : data.root representative ^ (2 * depth - 1) ≤ data.upper ^ depth := by
      exact (pow_le_pow_left₀ ratio_nonnegative (data.root_in_band representative).2 _).trans
        (pow_le_pow_of_le_one upper_nonnegative upper_lt_one.le (by
          have : 1 ≤ depth := (le_max_left _ _).trans depth_ge
          omega))
    have scaled := mul_le_mul_of_nonneg_left powers
      (mul_nonneg constant_nonnegative (show 0 ≤ (depth : ℝ) + 1 by positivity))
    simpa only [abs_sub_comm, mul_assoc] using bound.trans scaled

theorem rootFibreData_kernel_tendsto {exponent : ℝ} (data : RootFibreData exponent)
    (representative : ℕ → (ℕ → Bool × Bool) → (ℕ → Bool × Bool))
    (matching : ∀ depth digits index, index < depth → representative depth digits index = digits index)
    (digits : ℕ → Bool × Bool) :
    Tendsto (fun depth => rootKernelValue data (representative depth digits) digits depth)
      atTop (𝓝 (data.root digits)) := by
  obtain ⟨error, error_tendsto, estimate⟩ := rootFibreData_kernel_uniform_error data
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  · filter_upwards [estimate] with depth bound
    simpa only [Real.norm_eq_abs] using bound (representative depth digits) digits (matching depth digits)
  · exact error_tendsto

end LambdaCantor.First.Roots
