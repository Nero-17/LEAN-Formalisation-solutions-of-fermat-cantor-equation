import LambdaCantor.Circle.Onset

namespace LambdaCantor.Circle

/-- A geometric factor dominates every subsequent integer derivative factor. -/
theorem power_derivative_tail_bound {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (upper : ratio ≤ (1 / 2 : ℝ)) (offset : ℕ) :
    ((offset : ℝ) + 4) * ratio ^ (offset + 3) ≤ 4 * ratio ^ 3 := by
  induction offset with
  | zero => norm_num
  | succ offset inductionHypothesis =>
      have coefficient : ((offset : ℝ) + 5) * ratio ≤ (offset : ℝ) + 4 := by
        have := Nat.cast_nonneg (α := ℝ) offset
        nlinarith [mul_nonneg (show 0 ≤ (offset : ℝ) + 5 by positivity) (sub_nonneg.mpr upper)]
      have step := mul_le_mul_of_nonneg_right coefficient (pow_nonneg nonnegative (offset + 3))
      have power_identity : ratio ^ (offset + 1 + 3) = ratio ^ (offset + 3) * ratio := by
        rw [show offset + 1 + 3 = (offset + 3) + 1 by omega, pow_succ]
      simp only [Nat.cast_succ]
      rw [power_identity]
      nlinarith

/-- Coarse bounds suffice for a uniform transverse circle root, avoiding any
floating-point optimization of the derivative estimate. -/
theorem high_power_bounds {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (upper : ratio ≤ (7 / 25 : ℝ)) (exponent : ℕ) (large : 4 ≤ exponent) :
    ratio ^ exponent ≤ (1 / 100 : ℝ) ∧
    (exponent : ℝ) * ratio ^ (exponent - 1) ≤ (1 / 10 : ℝ) := by
  have small : ratio ≤ 1 := by linarith
  have fourth := power_antitone nonnegative small large
  have comparison := pow_le_pow_left₀ nonnegative upper 4
  constructor
  · norm_num at comparison
    linarith
  · obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le large
    have tail_bound := power_derivative_tail_bound nonnegative (by linarith) offset
    have third_bound := pow_le_pow_left₀ nonnegative upper 3
    have index : 4 + offset - 1 = offset + 3 := by omega
    rw [index, Nat.cast_add, Nat.cast_ofNat]
    norm_num at third_bound
    nlinarith

end LambdaCantor.Circle
