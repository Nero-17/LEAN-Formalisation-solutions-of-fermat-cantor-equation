import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor.First

/-- A quadratic Bernoulli lower bound, proved by induction rather than
assuming the Taylor remainder estimate used in Proposition 2.9. -/
theorem quadratic_bernoulli_lower (power : ℕ) {scale : ℝ}
    (hscale : 0 ≤ scale) (hscaleOne : scale ≤ 1) :
    ((power : ℝ) + 2) * ((power : ℝ) + 1) / 2 *
        (1 - scale) ^ power * scale ^ 2 ≤
      (1 - scale) ^ (power + 2) - 1 + ((power : ℝ) + 2) * scale := by
  induction power with
  | zero => norm_num; nlinarith [sq_nonneg scale]
  | succ power hind =>
    have hbase : 0 ≤ 1 - scale := by linarith
    have hbaseOne : 1 - scale ≤ 1 := by linarith
    have hpower : (1 - scale) ^ (power + 1) ≤ 1 :=
      pow_le_one₀ hbase hbaseOne
    have hmain := mul_le_mul_of_nonneg_left hind hbase
    have htail := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpower (by positivity : (0 : ℝ) ≤ (power : ℝ) + 2))
      (sq_nonneg scale)
    have hrecurrence : (1 - scale) ^ (power + 3) - 1 + ((power : ℝ) + 3) * scale =
        (1 - scale) * ((1 - scale) ^ (power + 2) - 1 + ((power : ℝ) + 2) * scale) +
          ((power : ℝ) + 2) * scale ^ 2 := by
      rw [show power + 3 = (power + 2) + 1 by omega, pow_succ]
      ring
    simp only [Nat.cast_succ, Nat.succ_eq_add_one] at *
    rw [show power + 1 + 2 = power + 3 by omega,
      show (power : ℝ) + 1 + 2 = (power : ℝ) + 3 by ring, hrecurrence]
    rw [pow_succ] at htail ⊢
    nlinarith

/-- The normalized curvature lower bound appearing at the quarter endpoint.
This is an unconditional polynomial inequality under the stated smallness
conditions, not a Taylor-remainder hypothesis. -/
theorem normalized_curvature_strict_lower (power : ℕ) {scale : ℝ}
    (hscale : 0 < scale) (hscaleOne : scale ≤ 1)
    (hsmall : (power : ℝ) * scale < 1 / 2) :
    ((power : ℝ) + 1) / 4 * scale <
      ((1 - scale) ^ (power + 2) - 1 + ((power : ℝ) + 2) * scale) /
        (((power : ℝ) + 2) * scale) := by
  have hquadratic := quadratic_bernoulli_lower power hscale.le hscaleOne
  have hbernoulli := one_add_mul_le_pow (a := -scale) (by linarith) power
  have hfactor : 1 / 2 < (1 - scale) ^ power := by
    have hbase : 1 + -scale = 1 - scale := by ring
    rw [hbase] at hbernoulli
    nlinarith
  have hdenominator : 0 < ((power : ℝ) + 2) * scale := by positivity
  apply (lt_div_iff₀ hdenominator).mpr
  have hpositive : 0 < (((power : ℝ) + 2) * ((power : ℝ) + 1) / 2) *
      ((1 - scale) ^ power - 1 / 2) * scale ^ 2 := by
    apply mul_pos
    · exact mul_pos (by positivity) (by linarith)
    · exact sq_pos_of_pos hscale
  nlinarith

end LambdaCantor.First



