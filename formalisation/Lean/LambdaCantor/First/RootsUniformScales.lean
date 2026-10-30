import LambdaCantor.First.RootsRootDisplacement
import LambdaCantor.First.ScaleComparison

noncomputable section
open Filter Topology
namespace LambdaCantor.First.Roots

theorem uniform_scale_ratio_of_exponential_closeness {lower upper constant : ℝ}
    (lower_positive : 0 < lower) (upper_nonnegative : 0 ≤ upper) (upper_lt_one : upper < 1) :
    ∃ minimumDepth : ℕ, ∀ depth : ℕ, minimumDepth ≤ depth → ∀ left right : ℝ,
      lower ≤ left → lower ≤ right → |right - left| ≤ constant * upper ^ depth →
      right ^ depth ≤ 2 * left ^ depth := by
  have convergence : Tendsto (fun depth : ℕ =>
      Real.exp ((lower⁻¹ * constant) * ((depth : ℝ) * upper ^ depth))) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, mul_zero, Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp
      ((tendsto_self_mul_const_pow_of_lt_one upper_nonnegative upper_lt_one).const_mul (lower⁻¹ * constant))
  obtain ⟨minimumDepth, uniform_bound⟩ := Filter.eventually_atTop.mp
    (Filter.Tendsto.eventually_lt_const (by norm_num : (1 : ℝ) < 2) convergence)
  refine ⟨minimumDepth, ?_⟩
  intro depth depth_ge left right left_lower right_lower close
  have left_positive := lower_positive.trans_le left_lower
  have right_positive := lower_positive.trans_le right_lower
  have logarithm_bound := log_parameter_lipschitz lower_positive left_lower right_lower
  have scaled_close := mul_le_mul_of_nonneg_left close (inv_nonneg.mpr lower_positive.le)
  have exponent_bound : (depth : ℝ) * (Real.log right - Real.log left) ≤
      (lower⁻¹ * constant) * ((depth : ℝ) * upper ^ depth) := by
    have bound := mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (logarithm_bound.trans scaled_close)) (Nat.cast_nonneg (α := ℝ) depth)
    nlinarith [bound]
  have exponential_bound := (Real.exp_le_exp.mpr exponent_bound).trans (uniform_bound depth depth_ge).le
  rw [mul_sub, Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log right_positive, Real.exp_log left_positive] at exponential_bound
  exact (div_le_iff₀ (pow_pos left_positive depth)).mp exponential_bound

theorem rootFibreData_uniform_scales {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ minimumDepth : ℕ, ∀ (left right : ℕ → Bool × Bool) (depth : ℕ), minimumDepth ≤ depth →
      (∀ index < depth, left index = right index) →
      data.root right ^ depth ≤ 2 * data.root left ^ depth := by
  obtain ⟨rootDepth, root_bound⟩ := rootFibreData_root_displacement data
  have lower_positive : 0 < data.lower := by linarith [data.lower_gt_quarter]
  have upper_nonnegative : 0 ≤ data.upper := lower_positive.le.trans data.ordered
  have upper_lt_one : data.upper < 1 := by linarith [data.upper_lt_half]
  have constant_nonnegative : 0 ≤ 4 * exponent / data.derivative_lower_bound := by
    apply div_nonneg
    · linarith [data.exponent_gt_one]
    · exact data.derivative_lower_bound_positive.le
  obtain ⟨scaleDepth, scale_bound⟩ := uniform_scale_ratio_of_exponential_closeness
    (constant := 4 * exponent / data.derivative_lower_bound) lower_positive upper_nonnegative upper_lt_one
  refine ⟨max rootDepth scaleDepth, ?_⟩
  intro left right depth depth_ge agreement
  apply scale_bound depth ((le_max_right _ _).trans depth_ge) _ _
    (data.root_in_band left).1 (data.root_in_band right).1
  have close := root_bound left right depth ((le_max_left _ _).trans depth_ge) agreement
  exact close.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (lower_positive.le.trans (data.root_in_band right).1)
      (data.root_in_band right).2 depth) constant_nonnegative)

end LambdaCantor.First.Roots
