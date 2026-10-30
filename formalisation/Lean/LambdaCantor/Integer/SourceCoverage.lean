import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace LambdaCantor.Integer

/-- The six printed ranges cover every exponent. This is only the indexing
part of the source certificate, not an assertion that the sources exist. -/
theorem exponent_ranges_cover (n : ℕ) (hn : 2 ≤ n) :
    (2 ≤ n ∧ n ≤ 300) ∨
    (301 ≤ n ∧ n ≤ 531440) ∨
    (3^12 ≤ n ∧ n < 3^13) ∨
    (3^13 ≤ n ∧ n < 3^14) ∨
    (3^14 ≤ n ∧ n < 3^15) ∨
    3^15 ≤ n := by
  norm_num
  omega

/-- Exact minimum Z used by the infinite-tail certificate. -/
theorem tail_minimum : (3 : ℚ)^15 * (20/243) = 1180980 := by norm_num

theorem tail_depth_condition : 11 + 3 ≤ (15 : ℕ) := by decide

/-- Pointwise comparison underlying the integral enclosure for every tail
parameter Z, without checking any finite sample of exponents. -/
theorem tail_integrand_bounds (minimum Z s : ℝ)
    (positive : 0 < minimum) (large : minimum ≤ Z) (nonnegative : 0 ≤ s) :
    minimum / (minimum+s) ≤ Z / (Z+s) ∧ Z / (Z+s) ≤ 1 := by
  have hmin : 0 < minimum+s := by linarith
  have hZ : 0 < Z+s := by linarith
  constructor
  · apply (div_le_div_iff₀ hmin hZ).mpr
    nlinarith
  · apply (div_le_iff₀ hZ).mpr
    linarith

end LambdaCantor.Integer
