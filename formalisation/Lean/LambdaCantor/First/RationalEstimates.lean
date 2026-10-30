import Mathlib.Algebra.Order.Ring.Pow
import LambdaCantor.Common
import LambdaCantor.First.Transverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor.First

/-- Elementary exponential estimate used at the left comparison endpoint. -/
theorem one_sub_exp_neg_le (increment : ℝ) :
    1 - Real.exp (-increment) ≤ increment := by
  have := Real.add_one_le_exp (-increment)
  linarith

/-- Quantitative loss when a comparison exponent is moved up by at most
one rational-lattice step. -/
theorem exponential_lattice_error {amplitude increment step : ℝ}
    (hamplitude : 0 ≤ amplitude) (hincrement : increment ≤ step) :
    amplitude * (1 - Real.exp (-increment)) ≤ amplitude * step := by
  exact mul_le_mul_of_nonneg_left
    ((one_sub_exp_neg_le increment).trans hincrement) hamplitude

/-- The power-four tail length in the frozen construction loses exactly
one sixteenth of the curvature scale. -/
theorem powers_four_tail_loss (r m : ℕ) :
    (4 : ℝ) ^ r * (1 / 4 : ℝ) ^ (m + r + 2) =
      (1 / 4 : ℝ) ^ m / 16 := by
  rw [pow_add, pow_add]
  have hcancel : (4 : ℝ) ^ r * (1 / 4 : ℝ) ^ r = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (4 : ℝ) ^ r * ((1 / 4 : ℝ) ^ m * (1 / 4 : ℝ) ^ r * (1 / 4 : ℝ) ^ 2) =
        ((4 : ℝ) ^ r * (1 / 4 : ℝ) ^ r) * (1 / 4 : ℝ) ^ m * (1 / 4 : ℝ) ^ 2 := by ring
    _ = (1 / 4 : ℝ) ^ m / 16 := by rw [hcancel]; ring

/-- Once the strict curvature lower bound is available, it dominates the
whole first-tail error for every exponent at least four. -/
theorem powers_four_residual_positive {exponent scale residual tailLoss : ℝ}
    (hexponent : 4 ≤ exponent) (hscale : 0 < scale)
    (hresidual : (exponent - 1) / 4 * scale < residual)
    (hloss : tailLoss ≤ scale / 16) : 0 < residual - tailLoss := by
  nlinarith

/-- Bernoulli lower bound used to keep the Taylor curvature factor uniformly
away from zero. The paper uses the stronger numeric bound 1/256. -/
theorem curvature_factor_lower (power : ℕ) {scale : ℝ}
    (hscale : scale ≤ 1) (hsmall : (power : ℝ) * scale < 1 / 2) :
    1 / 2 < (1 - scale) ^ power := by
  have hbernoulli := one_add_mul_le_pow (a := -scale) (by linarith) power
  have hbase : 1 + -scale = 1 - scale := by ring
  rw [hbase] at hbernoulli
  nlinarith

/-- Exact simplification of the mean-value estimate to the coefficient in
Theorem 2.7. -/
theorem denominator_coefficient_identity {exponent denominator : ℝ}
    (hexponent : 0 < exponent) (hdenominator : 0 < denominator) :
    ((3 / 4 : ℝ) ^ exponent * Real.log 4 / denominator) /
        (exponent * (2 : ℝ) ^ (1 - exponent)) =
      (3 / 2 : ℝ) ^ exponent * Real.log 4 / (2 * exponent * denominator) := by
  have hpower : (3 / 4 : ℝ) ^ exponent * (2 : ℝ) ^ exponent =
      (3 / 2 : ℝ) ^ exponent := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]
    norm_num
  rw [← hpower, Real.rpow_sub (by norm_num), Real.rpow_one]
  have htwo : (2 : ℝ) ^ exponent ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  field_simp [ne_of_gt hexponent, ne_of_gt hdenominator, htwo]
  <;> ring

end LambdaCantor.First




