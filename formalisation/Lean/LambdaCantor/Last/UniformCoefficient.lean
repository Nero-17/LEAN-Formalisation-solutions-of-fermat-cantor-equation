import LambdaCantor.Last.RealPowerLimit

noncomputable section
namespace LambdaCantor.Last
open Filter
open scoped Topology

/-- The varying near-axis coefficient preserves uniform convergence of the
vertical derivative factor over the whole unit interval. -/
theorem coefficient_power_factor_eventually_uniform {exponent coefficient : ℝ}
    {scales coefficients : ℕ → ℝ}
    (scales_nonnegative : ∀ index, 0 ≤ scales index)
    (scales_tendsto : Tendsto scales atTop (𝓝 0))
    (coefficients_tendsto : Tendsto coefficients atTop (𝓝 coefficient))
    {epsilon : ℝ} (epsilon_positive : 0 < epsilon) :
    ∀ᶠ index in atTop, ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
      |coefficients index*(1-scales index*coordinate)^(exponent-1)-coefficient| < epsilon := by
  have denominator_positive : 0 < 2*(|coefficient|+1) := by positivity
  have coefficient_small := Metric.tendsto_nhds.mp coefficients_tendsto
    (min 1 (epsilon/2)) (lt_min (by norm_num) (by positivity))
  have power_small := power_factor_eventually_uniform exponent scales_nonnegative scales_tendsto
    (div_pos epsilon_positive denominator_positive)
  filter_upwards [coefficient_small, power_small] with index coefficient_close power_close
  simp only [Real.dist_eq] at coefficient_close
  have coefficient_error : |coefficients index-coefficient| < epsilon/2 :=
    coefficient_close.trans_le (min_le_right _ _)
  have coefficient_bound : |coefficients index| ≤ |coefficient|+1 := by
    have triangle := abs_add_le (coefficients index-coefficient) coefficient
    have error_one := coefficient_close.trans_le (min_le_left _ _)
    simpa only [sub_add_cancel] using triangle.trans (by linarith :
      |coefficients index-coefficient|+|coefficient| ≤ |coefficient|+1)
  intro coordinate coordinate_bounds
  have power_error := power_close coordinate coordinate_bounds
  have factor_bound : |coefficients index| *
      |(1-scales index*coordinate)^(exponent-1)-1| < epsilon/2 := by
    have first_bound := mul_le_mul_of_nonneg_right coefficient_bound
      (abs_nonneg ((1-scales index*coordinate)^(exponent-1)-1))
    have second_bound := mul_lt_mul_of_pos_left power_error
      (show 0 < |coefficient|+1 by positivity)
    have cancellation : (|coefficient|+1)*(epsilon/(2*(|coefficient|+1))) = epsilon/2 := by
      field_simp [show |coefficient|+1 ≠ 0 by positivity]
      <;> ring
    rw [cancellation] at second_bound
    exact first_bound.trans_lt second_bound
  calc
    |coefficients index*(1-scales index*coordinate)^(exponent-1)-coefficient| =
        |coefficients index*((1-scales index*coordinate)^(exponent-1)-1)+
          (coefficients index-coefficient)| := by congr 1 <;> ring
    _ ≤ |coefficients index*((1-scales index*coordinate)^(exponent-1)-1)|+
        |coefficients index-coefficient| := abs_add_le _ _
    _ < epsilon := by rw [abs_mul]; linarith

end LambdaCantor.Last

