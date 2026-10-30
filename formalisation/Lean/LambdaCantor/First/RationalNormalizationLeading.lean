import LambdaCantor.First.RationalNormalizationFinite
import Mathlib.Algebra.Order.Ring.Abs

noncomputable section
namespace LambdaCantor.First

/-- Powers of the actual left full-tail factor approach one at the tail scale. -/
theorem powersFourLeftFactor_power_deviation_bound {ratio upper : ℝ}
    (hpos : 0 < ratio) (hratio : ratio ≤ upper) (hupper : upper < 1)
    (padding exponent : ℕ) (digits : ℕ → Bool) :
    |powersFourLeftFactor padding digits ratio ^ exponent - 1| ≤
      (exponent : ℝ) * upper ^ padding := by
  have hunit := (powersFour_factors_mem_unit hpos.le (hratio.trans_lt hupper) padding digits).1
  have hpower := abs_pow_sub_pow_le
    (a := powersFourLeftFactor padding digits ratio) (b := (1 : ℝ)) (n := exponent)
  simp only [one_pow, abs_one, abs_of_nonneg hunit.1, max_eq_right hunit.2, mul_one] at hpower
  calc
    _ ≤ |powersFourLeftFactor padding digits ratio - 1| * (exponent : ℝ) := hpower
    _ ≤ upper ^ padding * (exponent : ℝ) :=
      mul_le_mul_of_nonneg_right
        (powersFour_factor_deviation_bound hpos.le hratio hupper padding digits).1 (Nat.cast_nonneg _)
    _ = _ := mul_comm _ _

/-- Actual left-factor powers have uniformly vanishing derivatives. -/
theorem powersFourLeftFactor_power_derivative_bound {ratio upper : ℝ}
    (hpos : 0 < ratio) (hratio : ratio ≤ upper) (hupper : upper < 1)
    (padding exponent : ℕ) (digits : ℕ → Bool) :
    |deriv (fun parameter => powersFourLeftFactor padding digits parameter ^ exponent) ratio| ≤
      (exponent : ℝ) * ((padding : ℝ) * upper ^ (padding - 1) +
        upper ^ padding * addressParameterDerivativeBound upper) := by
  have hlt := hratio.trans_lt hupper
  have hunit := (powersFour_factors_mem_unit hpos.le hlt padding digits).1
  have hderivative := powersFourLeftFactor_derivative_bound hpos hratio hupper padding digits
  rw [(hasDerivAt_powersFourLeftFactor hpos hlt padding digits).deriv] at hderivative
  have h := scaled_power_derivative_bound 0 exponent (powersFourLeftFactor padding digits)
    hpos.le hratio (hasDerivAt_powersFourLeftFactor hpos hlt padding digits)
    (by simpa only [abs_of_nonneg hunit.1] using hunit.2) hderivative
  simpa only [pow_zero, one_mul, Nat.cast_zero, zero_mul, zero_add, mul_one] using h

/-- Uniform convergence of the left leading power, simultaneously in every tail. -/
theorem tendstoUniformly_powersFourLeftFactor_power {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : upper < 1) (hordered : lower ≤ upper)
    (padding : ℕ → ℕ) (hpadding : Filter.Tendsto padding Filter.atTop Filter.atTop)
    (exponent : ℕ) :
    TendstoUniformly
      (fun index (point : Set.Icc lower upper × (ℕ → Bool)) =>
        powersFourLeftFactor (padding index) point.2 point.1 ^ exponent)
      (fun _ => (1 : ℝ)) Filter.atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  have hlimit := ((tendsto_pow_atTop_nhds_zero_of_lt_one
    (hlower.le.trans hordered) hupper).comp hpadding).const_mul (exponent : ℝ)
  simp only [mul_zero] at hlimit
  filter_upwards [hlimit.eventually (gt_mem_nhds hepsilon)] with index hindex
  intro point
  rw [Real.dist_eq, abs_sub_comm]
  exact (powersFourLeftFactor_power_deviation_bound (hlower.trans_le point.1.property.1)
    point.1.property.2 hupper (padding index) exponent point.2).trans_lt hindex

/-- Uniform convergence of the left leading power in the derivative norm. -/
theorem tendstoUniformly_powersFourLeftFactor_power_derivative {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : upper < 1) (hordered : lower ≤ upper)
    (padding : ℕ → ℕ) (hpadding : Filter.Tendsto padding Filter.atTop Filter.atTop)
    (exponent : ℕ) :
    TendstoUniformly
      (fun index (point : Set.Icc lower upper × (ℕ → Bool)) =>
        deriv (fun parameter => powersFourLeftFactor (padding index) point.2 parameter ^ exponent) point.1)
      (fun _ => (0 : ℝ)) Filter.atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  have hlimit := ((tendsto_scaled_address_derivative_majorant
    (hlower.trans_le hordered) hupper).comp hpadding).const_mul (exponent : ℝ)
  simp only [mul_zero] at hlimit
  filter_upwards [hlimit.eventually (gt_mem_nhds hepsilon)] with index hindex
  intro point
  simp only [dist_zero_left, Real.norm_eq_abs]
  exact (powersFourLeftFactor_power_derivative_bound (hlower.trans_le point.1.property.1)
    point.1.property.2 hupper (padding index) exponent point.2).trans_lt hindex

end LambdaCantor.First
