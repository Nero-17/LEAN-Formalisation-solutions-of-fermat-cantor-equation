import LambdaCantor.AE.CenteredFullSecond
import LambdaCantor.AE.CenteredFactorSecondLimit
import LambdaCantor.AE.CenteredUniform

noncomputable section
open Filter
open scoped Topology

namespace LambdaCantor.AE

theorem centeredNormalizedSecond_limit
    {exponent center lower upper discrepancy : ℝ}
    (center_positive : 0 < center) (lower_positive : 0 < lower)
    (ordered : lower ≤ upper) (upper_less_one : upper < 1)
    (horizontalDepth verticalDepth : ℕ → ℕ)
    (ratios : ℕ → ℝ) (ratios_mem : ∀ index, ratios index ∈ Set.Icc lower upper)
    (ratios_limit : Tendsto ratios atTop (𝓝 center)) (digits : ℕ → ℕ → Bool × Bool)
    (phase_limit : Tendsto (fun index => (verticalDepth index : ℝ)-exponent*horizontalDepth index)
      atTop (𝓝 discrepancy))
    (remainder_limit : Tendsto (fun index => centeredRemainderSecond exponent (horizontalDepth index)
      (verticalDepth index) index (fun position => (digits index position).2) (ratios index)) atTop (𝓝 0)) :
    Tendsto (fun index => centeredNormalizedSecond exponent (horizontalDepth index)
      (verticalDepth index) index (digits index) (ratios index)) atTop
      (𝓝 (-exponent*discrepancy*(discrepancy-1)*center^(discrepancy-2))) := by
  obtain ⟨secondBound, _, second_uniform⟩ :=
    centered_address_uniform_second_bound (lower_positive.trans_le ordered) upper_less_one
  have first_bounds (coordinate : Bool) : ∀ index,
      |deriv (fun parameter => address parameter (fun position =>
        if coordinate then (digits index position).1 else (digits index position).2)) (ratios index)| ≤
          addressParameterDerivativeBound upper := by
    intro index
    rw [(hasDerivAt_address_parameter (lower_positive.trans_le (ratios_mem index).1)
      ((ratios_mem index).2.trans_lt upper_less_one) _).deriv]
    exact address_parameter_derivative_bound (lower_positive.le.trans (ratios_mem index).1)
      (ratios_mem index).2 upper_less_one _
  have second_bounds (coordinate : Bool) : ∀ index,
      |deriv (deriv (fun parameter => address parameter (fun position =>
        if coordinate then (digits index position).1 else (digits index position).2))) (ratios index)| ≤ secondBound := by
    intro index
    exact second_uniform _ _ ⟨lower_positive.trans_le (ratios_mem index).1, (ratios_mem index).2⟩
  have horizontal := (centered_factors_tendsto_one lower_positive ordered upper_less_one
    ratios ratios_mem (fun index position => (digits index position).1)).1
  have tail := (centered_factors_tendsto_one lower_positive ordered upper_less_one
    ratios ratios_mem (fun index position => (digits index position).2)).2
  have horizontal_first := (centeredFactorFirst_tendsto_zero lower_positive ordered upper_less_one
    ratios ratios_mem (fun index position => (digits index position).1)).1
  have tail_first := (centeredFactorFirst_tendsto_zero lower_positive ordered upper_less_one
    ratios ratios_mem (fun index position => (digits index position).2)).2
  have horizontal_second := (centeredFactorSecond_tendsto_zero lower_positive ordered upper_less_one
    ratios ratios_mem (fun index position => (digits index position).1)
      (by simpa using first_bounds true)
      (by simpa using second_bounds true)).1
  have tail_second := (centeredFactorSecond_tendsto_zero lower_positive ordered upper_less_one
    ratios ratios_mem (fun index position => (digits index position).2)
      (by simpa using first_bounds false)
      (by simpa using second_bounds false)).2
  have horizontal_term :=
    ((horizontal.rpow_const (p := exponent-2) (Or.inl (by norm_num))).mul (horizontal_first.pow 2)).const_mul
      (exponent*(exponent-1))
  have horizontal_second_term :=
    ((horizontal.rpow_const (p := exponent-1) (Or.inl (by norm_num))).mul horizontal_second).const_mul exponent
  have linear_term := ((phase_limit.mul (phase_limit.sub_const 1)).mul
    (ratios_limit.rpow (phase_limit.sub_const 2) (Or.inl center_positive.ne'))).mul tail
  have linear_mixed := ((phase_limit.mul
    (ratios_limit.rpow (phase_limit.sub_const 1) (Or.inl center_positive.ne'))).mul tail_first).const_mul 2
  have linear_second := (ratios_limit.rpow phase_limit (Or.inl center_positive.ne')).mul tail_second
  have limit := ((horizontal_term.add horizontal_second_term).sub
    (((linear_term.add linear_mixed).add linear_second).const_mul exponent)).add remainder_limit
  simpa only [centeredNormalizedSecond, zero_pow (by decide : 2 ≠ 0),
    Real.one_rpow, one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add,
    zero_sub, neg_mul, mul_assoc] using limit

/-- The complete normalized second derivative is uniformly bounded on the
shrinking root window, over every address and hence over every frozen prefix. -/
theorem centered_uniform_second_derivative_bound
    {exponent center lower upper width : ℝ}
    (center_positive : 0 < center) (center_less_one : center < 1)
    (lower_positive : 0 < lower) (center_mem : center ∈ Set.Icc lower upper)
    (upper_less_one : upper < 1) (width_nonnegative : 0 ≤ width)
    (horizontalDepth verticalDepth : ℕ → ℕ)
    (phase_approximation : ∀ index, |(verticalDepth index : ℝ)-exponent*horizontalDepth index +
      Real.log exponent/Real.log center| ≤ (center^index)^2)
    (remainder_limit : ∀ ratios : ℕ → ℝ, (∀ index, ratios index ∈ Set.Icc lower upper) →
      ∀ digits : ℕ → ℕ → Bool,
        Tendsto (fun index => centeredRemainderSecond exponent (horizontalDepth index)
          (verticalDepth index) index (digits index) (ratios index)) atTop (𝓝 0)) :
    ∀ᶠ index : ℕ in atTop, ∀ digits ratio,
      ratio ∈ Set.Icc lower upper → |ratio-center| ≤ width*center^index →
      |centeredNormalizedSecond exponent (horizontalDepth index) (verticalDepth index) index digits ratio| ≤
        |-exponent*(-Real.log exponent/Real.log center)*
          (-Real.log exponent/Real.log center-1)*center^(-Real.log exponent/Real.log center-2)|+1 := by
  apply centered_eventually_uniform_abs_bound
    (fun index digits ratio => centeredNormalizedSecond exponent (horizontalDepth index)
      (verticalDepth index) index digits ratio)
    center_mem width_nonnegative (fun index => center^index) (fun _ => pow_nonneg center_positive.le _)
    (tendsto_pow_atTop_nhds_zero_of_lt_one center_positive.le center_less_one)
  intro digits ratios ratios_mem ratios_limit
  apply centeredNormalizedSecond_limit center_positive lower_positive (center_mem.1.trans center_mem.2)
    upper_less_one horizontalDepth verticalDepth ratios ratios_mem ratios_limit digits
  · apply centered_phase_tendsto center_positive center_less_one horizontalDepth verticalDepth
    intro index
    simpa only [neg_div, sub_neg_eq_add] using phase_approximation index
  · exact remainder_limit ratios ratios_mem (fun index position => (digits index position).2)

end LambdaCantor.AE
