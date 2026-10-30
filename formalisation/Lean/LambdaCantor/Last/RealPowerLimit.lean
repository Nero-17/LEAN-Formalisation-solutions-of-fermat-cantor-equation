import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

noncomputable section
namespace LambdaCantor.Last
open Filter
open scoped Topology

/-- The real-power drop has its expected first-order limit. No integrality of
its exponent is needed. -/
theorem real_power_drop_limit (exponent coordinate : ℝ) :
    Tendsto (fun scale : ℝ => (1-(1-scale*coordinate)^exponent)/scale)
      (𝓝[>] 0) (𝓝 (exponent*coordinate)) := by
  have affine_derivative :=
    ((hasDerivAt_id (0 : ℝ)).mul_const coordinate).const_sub (1 : ℝ)
  have power_derivative := affine_derivative.rpow_const
    (p := exponent) (Or.inl (by norm_num))
  have drop_derivative := power_derivative.const_sub (1 : ℝ)
  have normalized_derivative := drop_derivative.congr_deriv (g' := exponent * coordinate)
    (by simp <;> ring)
  simpa only [id_eq, zero_add, zero_mul, mul_zero, sub_zero, Real.one_rpow, sub_self,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using normalized_derivative.tendsto_slope_zero_right

/-- Pointwise convergence of the normalized curve along arbitrary positive
scales tending to zero and coefficients tending to a prescribed limit. -/
theorem normalized_power_curve_limit {exponent coefficient : ℝ}
    (exponent_nonzero : exponent ≠ 0) {scales coefficients : ℕ → ℝ}
    (scales_positive : ∀ index, 0 < scales index)
    (scales_tendsto : Tendsto scales atTop (𝓝 0))
    (coefficients_tendsto : Tendsto coefficients atTop (𝓝 coefficient))
    (first second : ℝ) :
    Tendsto (fun index => first^exponent - coefficients index/exponent *
      ((1-(1-scales index*second)^exponent)/scales index))
      atTop (𝓝 (first^exponent-coefficient*second)) := by
  have scales_within : Tendsto scales atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ scales_tendsto
      (Eventually.of_forall scales_positive)
  have drop_tendsto := (real_power_drop_limit exponent second).comp scales_within
  have limit := (tendsto_const_nhds (x := first ^ exponent)).sub
    ((coefficients_tendsto.div_const exponent).mul drop_tendsto)
  have value : first^exponent - coefficient/exponent*(exponent*second) =
      first^exponent-coefficient*second := by
    rw [← mul_assoc, div_mul_cancel₀ _ exponent_nonzero]
  simpa only [value, Function.comp_apply] using limit

/-- Pointwise convergence of the second partial derivative expression. The
uniform-on-rectangle upgrade is a separate obligation. -/
theorem normalized_power_partial_limit {exponent coefficient : ℝ}
    {scales coefficients : ℕ → ℝ}
    (scales_tendsto : Tendsto scales atTop (𝓝 0))
    (coefficients_tendsto : Tendsto coefficients atTop (𝓝 coefficient))
    (coordinate : ℝ) :
    Tendsto (fun index => coefficients index *
      (1-scales index*coordinate)^(exponent-1)) atTop (𝓝 coefficient) := by
  have base_tendsto : Tendsto (fun index => 1-scales index*coordinate)
      atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (scales_tendsto.mul_const coordinate)
  have power_tendsto := (Real.continuousAt_rpow_const
    (1 : ℝ) (exponent-1) (Or.inl one_ne_zero)).tendsto.comp base_tendsto
  simpa using coefficients_tendsto.mul power_tendsto

/-- The power factor in the vertical derivative approaches one uniformly
on the entire unit interval, with an explicit small-scale quantifier. -/
theorem power_factor_uniform_small_scale (exponent : ℝ) {epsilon : ℝ}
    (epsilon_positive : 0 < epsilon) :
    ∃ delta > 0, ∀ scale : ℝ, 0 ≤ scale → scale < delta →
      ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
        |(1-scale*coordinate)^(exponent-1)-1| < epsilon := by
  obtain ⟨delta, delta_positive, power_close⟩ := Metric.continuousAt_iff.mp
    (Real.continuousAt_rpow_const (1 : ℝ) (exponent-1) (Or.inl one_ne_zero))
    epsilon epsilon_positive
  refine ⟨delta, delta_positive, ?_⟩
  intro scale scale_nonnegative scale_small coordinate coordinate_bounds
  have distance_bound : dist (1-scale*coordinate) (1 : ℝ) < delta := by
    rw [Real.dist_eq, show (1-scale*coordinate)-1 = -(scale*coordinate) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg scale_nonnegative coordinate_bounds.1)]
    exact (mul_le_of_le_one_right scale_nonnegative coordinate_bounds.2).trans_lt scale_small
  simpa only [Real.dist_eq, Real.one_rpow] using power_close distance_bound

/-- The preceding uniform estimate remains uniform after substituting any
nonnegative sequence of scales tending to zero. -/
theorem power_factor_eventually_uniform (exponent : ℝ) {scales : ℕ → ℝ}
    (scales_nonnegative : ∀ index, 0 ≤ scales index)
    (scales_tendsto : Tendsto scales atTop (𝓝 0)) {epsilon : ℝ}
    (epsilon_positive : 0 < epsilon) :
    ∀ᶠ index in atTop, ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
      |(1-scales index*coordinate)^(exponent-1)-1| < epsilon := by
  obtain ⟨delta, delta_positive, uniform_estimate⟩ :=
    power_factor_uniform_small_scale exponent epsilon_positive
  filter_upwards [scales_tendsto.eventually (gt_mem_nhds delta_positive)] with index scale_small
  exact uniform_estimate (scales index) (scales_nonnegative index) scale_small
/-- Uniform divided-difference convergence on the unit interval follows
from the one-variable derivative at zero; the zero coordinate is handled
separately, so no division by it enters the statement. -/
theorem real_power_drop_uniform_small_scale (exponent : ℝ) {epsilon : ℝ}
    (epsilon_positive : 0 < epsilon) :
    ∃ delta > 0, ∀ scale : ℝ, 0 < scale → scale < delta →
      ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
        |(1-(1-scale*coordinate)^exponent)/scale-exponent*coordinate| < epsilon := by
  obtain ⟨delta, delta_positive, drop_close⟩ := Metric.tendsto_nhdsWithin_nhds.mp
    (real_power_drop_limit exponent 1) epsilon epsilon_positive
  refine ⟨delta, delta_positive, ?_⟩
  intro scale scale_positive scale_small coordinate coordinate_bounds
  rcases eq_or_lt_of_le coordinate_bounds.1 with coordinate_zero | coordinate_positive
  · subst coordinate
    simpa using epsilon_positive
  · have product_positive : 0 < scale*coordinate := mul_pos scale_positive coordinate_positive
    have product_small : dist (scale*coordinate) (0 : ℝ) < delta := by
      rw [Real.dist_eq, sub_zero, abs_of_pos product_positive]
      exact (mul_le_of_le_one_right scale_positive.le coordinate_bounds.2).trans_lt scale_small
    have approximation := drop_close product_positive product_small
    simp only [mul_one, Real.dist_eq] at approximation
    have factorization : (1-(1-scale*coordinate)^exponent)/scale-exponent*coordinate =
        coordinate*((1-(1-scale*coordinate)^exponent)/(scale*coordinate)-exponent) := by
      field_simp [scale_positive.ne', coordinate_positive.ne']
      <;> ring
    rw [factorization, abs_mul, abs_of_pos coordinate_positive]
    exact (mul_le_of_le_one_left (abs_nonneg _) coordinate_bounds.2).trans_lt approximation

/-- Both uniform estimates needed for the normalized real-power curve hold
for one common small-scale bound. -/
theorem real_power_uniform_value_and_partial (exponent : ℝ) {epsilon : ℝ}
    (epsilon_positive : 0 < epsilon) :
    ∃ delta > 0, ∀ scale : ℝ, 0 < scale → scale < delta →
      ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
        |(1-(1-scale*coordinate)^exponent)/scale-exponent*coordinate| < epsilon ∧
        |(1-scale*coordinate)^(exponent-1)-1| < epsilon := by
  obtain ⟨value_delta, value_positive, value_estimate⟩ :=
    real_power_drop_uniform_small_scale exponent epsilon_positive
  obtain ⟨partial_delta, partial_positive, partial_estimate⟩ :=
    power_factor_uniform_small_scale exponent epsilon_positive
  refine ⟨min value_delta partial_delta, lt_min value_positive partial_positive, ?_⟩
  intro scale scale_positive scale_small coordinate coordinate_bounds
  exact ⟨value_estimate scale scale_positive (lt_of_lt_of_le scale_small (min_le_left _ _))
    coordinate coordinate_bounds,
    partial_estimate scale scale_positive.le (lt_of_lt_of_le scale_small (min_le_right _ _))
      coordinate coordinate_bounds⟩

/-- Substitution of any escaping near-axis scale preserves both estimates
uniformly; this statement is independent of the chosen irrational approximation. -/
theorem real_power_eventually_uniform_value_and_partial (exponent : ℝ)
    {scales : ℕ → ℝ} (scales_positive : ∀ index, 0 < scales index)
    (scales_tendsto : Tendsto scales atTop (𝓝 0)) {epsilon : ℝ}
    (epsilon_positive : 0 < epsilon) :
    ∀ᶠ index in atTop, ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
      |(1-(1-scales index*coordinate)^exponent)/scales index-exponent*coordinate| < epsilon ∧
      |(1-scales index*coordinate)^(exponent-1)-1| < epsilon := by
  obtain ⟨delta, delta_positive, uniform_estimate⟩ :=
    real_power_uniform_value_and_partial exponent epsilon_positive
  filter_upwards [scales_tendsto.eventually (gt_mem_nhds delta_positive)] with index scale_small
  exact uniform_estimate (scales index) (scales_positive index) scale_small
end LambdaCantor.Last





