import LambdaCantor.First.AddressParameter
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Ring

namespace LambdaCantor

theorem hasDerivAt_scaled_address {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1)
    (length : ℕ) (digits : ℕ → Bool) :
    HasDerivAt (fun parameter => parameter ^ length * address parameter digits)
      ((length : ℝ) * ratio ^ (length - 1) * address ratio digits +
        ratio ^ length * addressParameterDerivative ratio digits) ratio := by
  simpa only [mul_one] using! ((hasDerivAt_id ratio).pow length).mul
    (hasDerivAt_address_parameter hpos hlt digits)

theorem scaled_address_derivative_bound {ratio upper : ℝ}
    (hpos : 0 < ratio) (hratio : ratio ≤ upper) (hupper : upper < 1)
    (length : ℕ) (digits : ℕ → Bool) :
    |deriv (fun parameter => parameter ^ length * address parameter digits) ratio| ≤
      (length : ℝ) * upper ^ (length - 1) +
        upper ^ length * addressParameterDerivativeBound upper := by
  have hlt := lt_of_le_of_lt hratio hupper
  have hnonnegative := address_nonnegative hpos.le hlt digits
  have hle := address_le_one hpos.le hlt digits
  have hderivative := address_parameter_derivative_bound hpos.le hratio hupper digits
  have hbound_nonnegative : 0 ≤ addressParameterDerivativeBound upper :=
    (abs_nonneg _).trans hderivative
  rw [(hasDerivAt_scaled_address hpos hlt length digits).deriv]
  calc
    _ ≤ |(length : ℝ) * ratio ^ (length - 1) * address ratio digits| +
        |ratio ^ length * addressParameterDerivative ratio digits| := abs_add_le _ _
    _ = (length : ℝ) * ratio ^ (length - 1) * address ratio digits +
        ratio ^ length * |addressParameterDerivative ratio digits| := by
      rw [abs_of_nonneg (by positivity : 0 ≤ (length : ℝ) * ratio ^ (length - 1) * address ratio digits),
        abs_mul, abs_of_nonneg (pow_nonneg hpos.le length)]
    _ ≤ (length : ℝ) * ratio ^ (length - 1) * 1 +
        ratio ^ length * addressParameterDerivativeBound upper :=
      add_le_add (mul_le_mul_of_nonneg_left hle (by positivity))
        (mul_le_mul_of_nonneg_left hderivative (pow_nonneg hpos.le length))
    _ ≤ _ := by
      simp only [mul_one]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos.le hratio (length - 1)) (Nat.cast_nonneg length))
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hpos.le hratio length) hbound_nonnegative)

/-- The explicit uniform derivative majorant tends to zero with the prefix
length; the factor length does not obstruct exponential decay. -/
theorem tendsto_scaled_address_derivative_majorant {upper : ℝ}
    (hpos : 0 < upper) (hlt : upper < 1) :
    Filter.Tendsto (fun length : ℕ =>
      (length : ℝ) * upper ^ (length - 1) +
        upper ^ length * addressParameterDerivativeBound upper)
      Filter.atTop (nhds (0 : ℝ)) := by
  have hfirst := (tendsto_self_mul_const_pow_of_lt_one hpos.le hlt).div_const upper
  have hsecond := (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt).mul_const
    (addressParameterDerivativeBound upper)
  convert hfirst.add hsecond using 1
  · funext length
    by_cases hzero : length = 0
    · simp [hzero]
    · have hlength : length - 1 + 1 = length := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hzero)
      have hpower : upper ^ length = upper ^ (length - 1) * upper := by
        rw [← pow_succ, hlength]
      rw [hpower]
      field_simp
  · simp

/-- Scaled full address tails vanish uniformly in both the parameter and all
binary addresses on a positive compact band. -/
theorem tendstoUniformly_scaled_address {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : upper < 1) (hordered : lower ≤ upper) :
    TendstoUniformly
      (fun length (point : Set.Icc lower upper × (ℕ → Bool)) =>
        (point.1 : ℝ) ^ length * address point.1 point.2)
      (fun _ => (0 : ℝ)) Filter.atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  have hnonnegative : 0 ≤ upper := hlower.le.trans hordered
  have hlimit := tendsto_pow_atTop_nhds_zero_of_lt_one hnonnegative hupper
  filter_upwards [hlimit.eventually (gt_mem_nhds hepsilon)] with length hlength
  intro point
  have hratio : 0 ≤ (point.1 : ℝ) := hlower.le.trans point.1.property.1
  have hlt : (point.1 : ℝ) < 1 := lt_of_le_of_lt point.1.property.2 hupper
  have hvalue_nonnegative := address_nonnegative hratio hlt point.2
  have hvalue_le := address_le_one hratio hlt point.2
  simp only [dist_zero_left, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg hratio length) hvalue_nonnegative)]
  apply lt_of_le_of_lt _ hlength
  calc
    _ ≤ (point.1 : ℝ) ^ length * 1 :=
      mul_le_mul_of_nonneg_left hvalue_le (pow_nonneg hratio length)
    _ ≤ upper ^ length := by
      simpa only [mul_one] using pow_le_pow_left₀ hratio point.1.property.2 length

/-- The full tails vanish in C1: their parameter derivatives converge
uniformly, simultaneously over every binary address. -/
theorem tendstoUniformly_scaled_address_derivative {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : upper < 1) (hordered : lower ≤ upper) :
    TendstoUniformly
      (fun length (point : Set.Icc lower upper × (ℕ → Bool)) =>
        deriv (fun parameter => parameter ^ length * address parameter point.2) point.1)
      (fun _ => (0 : ℝ)) Filter.atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  have hlimit := tendsto_scaled_address_derivative_majorant
    (lt_of_lt_of_le hlower hordered) hupper
  filter_upwards [hlimit.eventually (gt_mem_nhds hepsilon)] with length hlength
  intro point
  simp only [dist_zero_left, Real.norm_eq_abs]
  exact lt_of_le_of_lt (scaled_address_derivative_bound
    (lt_of_lt_of_le hlower point.1.property.1) point.1.property.2 hupper length point.2) hlength

end LambdaCantor

