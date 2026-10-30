import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open scoped BigOperators
namespace LambdaCantor.First

/-- Exact binomial expansion with its constant and linear terms removed. -/
theorem binomial_remainder_expansion (exponent : ℕ) (hexponent : 2 ≤ exponent)
    (increment : ℝ) :
    (1 - increment) ^ exponent = 1 - (exponent : ℝ) * increment +
      ∑ index ∈ Finset.range (exponent - 1),
        (-increment) ^ (index + 2) * (exponent.choose (index + 2) : ℝ) := by
  have hexpansion := add_pow (-increment) (1 : ℝ) exponent
  simp only [one_pow, mul_one] at hexpansion
  rw [show exponent + 1 = (exponent - 1 + 1) + 1 by omega,
    Finset.sum_range_succ', Finset.sum_range_succ'] at hexpansion
  simp only [zero_add, pow_zero, pow_one, Nat.choose_zero_right,
    Nat.choose_one_right, Nat.cast_one, one_mul, add_zero] at hexpansion
  have hleft : -increment + 1 = 1 - increment := by ring
  rw [hleft] at hexpansion
  simp only [Nat.add_assoc] at hexpansion
  linarith

/-- Exact normalization of the polynomial residual. No limiting statement,
positivity hypothesis, or division is used here. The lattice equation makes
every remainder exponent nonnegative. -/
theorem integer_residual_factorization
    (exponent leftDepth rightDepth phase : ℕ) (hexponent : 2 ≤ exponent)
    (hdepth : rightDepth = exponent * leftDepth + phase)
    (ratio leftFactor rightFactor : ℝ) :
    (ratio ^ leftDepth * leftFactor) ^ exponent +
        (1 - ratio ^ rightDepth * rightFactor) ^ exponent - 1 =
      ratio ^ (exponent * leftDepth) *
        (leftFactor ^ exponent - (exponent : ℝ) * ratio ^ phase * rightFactor +
          ∑ index ∈ Finset.range (exponent - 1),
            ratio ^ ((index + 1) * rightDepth + phase) *
              (-rightFactor) ^ (index + 2) * (exponent.choose (index + 2) : ℝ)) := by
  have hleft : (ratio ^ leftDepth * leftFactor) ^ exponent =
      ratio ^ (exponent * leftDepth) * leftFactor ^ exponent := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm leftDepth exponent]
  have hlinear : ratio ^ (exponent * leftDepth) *
      ((exponent : ℝ) * ratio ^ phase * rightFactor) =
        (exponent : ℝ) * ratio ^ rightDepth * rightFactor := by
    rw [hdepth, pow_add]
    ring
  have hterm (index : ℕ) : ratio ^ (exponent * leftDepth) *
      (ratio ^ ((index + 1) * rightDepth + phase) *
        (-rightFactor) ^ (index + 2) * (exponent.choose (index + 2) : ℝ)) =
      (-(ratio ^ rightDepth * rightFactor)) ^ (index + 2) *
        (exponent.choose (index + 2) : ℝ) := by
    have hpowers : exponent * leftDepth + ((index + 1) * rightDepth + phase) =
        rightDepth * (index + 2) := by rw [hdepth]; ring
    calc
      _ = ratio ^ (exponent * leftDepth + ((index + 1) * rightDepth + phase)) *
          (-rightFactor) ^ (index + 2) * (exponent.choose (index + 2) : ℝ) := by
        rw [pow_add]
        ring
      _ = _ := by
        rw [hpowers, pow_mul, ← mul_pow]
        congr 2
        ring
  have hsum : ratio ^ (exponent * leftDepth) *
      (∑ index ∈ Finset.range (exponent - 1),
        ratio ^ ((index + 1) * rightDepth + phase) *
          (-rightFactor) ^ (index + 2) * (exponent.choose (index + 2) : ℝ)) =
      ∑ index ∈ Finset.range (exponent - 1),
        (-(ratio ^ rightDepth * rightFactor)) ^ (index + 2) *
          (exponent.choose (index + 2) : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun index _ => hterm index)
  rw [hleft, binomial_remainder_expansion exponent hexponent,
    mul_add, mul_sub, hlinear, hsum]
  ring

/-- Exact finite-sum normalized residual for the full two-tail cylinders of
the powers-four proof. The tails are arbitrary real values, so substitution
of actual Cantor addresses requires no further algebraic assumptions. -/
theorem powers_four_full_tail_normalization
    (exponent leftDepth rightDepth phase padding : ℕ) (hexponent : 2 ≤ exponent)
    (hdepth : rightDepth = exponent * leftDepth + phase)
    (ratio leftTail rightTail : ℝ) (hratio : ratio ≠ 0) :
    ((ratio ^ leftDepth * (1 - ratio ^ padding + ratio ^ padding * leftTail)) ^ exponent +
      (1 - ratio ^ rightDepth + ratio ^ (rightDepth + padding) * rightTail) ^ exponent - 1) /
        ratio ^ (exponent * leftDepth) =
      (1 - ratio ^ padding + ratio ^ padding * leftTail) ^ exponent -
        (exponent : ℝ) * ratio ^ phase * (1 - ratio ^ padding * rightTail) +
        ∑ index ∈ Finset.range (exponent - 1),
          ratio ^ ((index + 1) * rightDepth + phase) *
            (-(1 - ratio ^ padding * rightTail)) ^ (index + 2) *
              (exponent.choose (index + 2) : ℝ) := by
  have hright : 1 - ratio ^ rightDepth + ratio ^ (rightDepth + padding) * rightTail =
      1 - ratio ^ rightDepth * (1 - ratio ^ padding * rightTail) := by
    rw [pow_add]
    ring
  rw [hright, integer_residual_factorization exponent leftDepth rightDepth phase hexponent hdepth]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ hratio)

end LambdaCantor.First
