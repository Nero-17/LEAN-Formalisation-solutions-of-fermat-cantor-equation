import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace LambdaCantor

/-- Uniform quadratic remainder near the positive base 1, for every real
exponent. The constant depends only on the exponent. -/
theorem exists_rpow_quadratic_remainder_bound (exponent : ℝ) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ scale ∈ Set.Icc (0 : ℝ) (1 / 2),
      |(1 - scale) ^ exponent - 1 + exponent * scale| ≤ constant * scale ^ 2 := by
  have hsmooth : ContDiffOn ℝ (1 + 1 : ℕ)
      (fun scale : ℝ => (1 - scale) ^ exponent) (Set.Icc 0 (1 / 2)) := by
    apply (contDiffOn_const.sub contDiffOn_id).rpow_const_of_ne
    intro scale hscale
    change 1 - scale ≠ 0
    linarith [hscale.2]
  obtain ⟨constant, hbound⟩ := exists_taylor_mean_remainder_bound
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hsmooth
  have hderivative : HasDerivAt (fun scale : ℝ => (1 - scale) ^ exponent) (-exponent) 0 := by
    simpa using! (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
      (hasDerivAt_id (0 : ℝ))).rpow_const (p := exponent) (Or.inl (by norm_num)))
  have hwithin : derivWithin (fun scale : ℝ => (1 - scale) ^ exponent)
      (Set.Icc 0 (1 / 2)) 0 = -exponent :=
    hderivative.hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1 / 2)) 0 (by constructor <;> norm_num))
  refine ⟨max constant 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro scale hscale
  have h := hbound scale hscale
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_one,
    hwithin, sub_zero, Real.one_rpow, Nat.factorial_zero, Nat.cast_zero,
    zero_add, Nat.cast_one, one_mul, inv_one, pow_one, one_smul,
    smul_eq_mul, Real.norm_eq_abs] at h
  have heq : (1 - scale) ^ exponent - (1 + scale * -exponent) =
      (1 - scale) ^ exponent - 1 + exponent * scale := by ring
  rw [heq] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg scale))

/-- Uniform first-order control on the same compact interval. -/
theorem exists_rpow_linear_difference_bound (exponent : ℝ) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ scale ∈ Set.Icc (0 : ℝ) (1 / 2),
      |(1 - scale) ^ exponent - 1| ≤ constant * scale := by
  obtain ⟨constant, hpositive, hbound⟩ := exists_rpow_quadratic_remainder_bound exponent
  refine ⟨constant + |exponent|, by linarith [abs_nonneg exponent], ?_⟩
  intro scale hscale
  calc
    _ = |((1 - scale) ^ exponent - 1 + exponent * scale) - exponent * scale| := by ring_nf
    _ ≤ |(1 - scale) ^ exponent - 1 + exponent * scale| + |exponent * scale| := abs_sub _ _
    _ ≤ constant * scale ^ 2 + |exponent| * scale := by
      simpa only [abs_mul, abs_of_nonneg hscale.1, add_comm] using!
        add_le_add_right (hbound scale hscale) |exponent * scale|
    _ ≤ _ := by
      have hsq : scale ^ 2 ≤ scale := by nlinarith [hscale.1, hscale.2]
      nlinarith

/-- The derivative of the power remainder also has a uniform first-order
bound; this is the scalar C1 estimate used after substituting small tails. -/
theorem exists_rpow_derivative_remainder_bound (exponent : ℝ) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ scale ∈ Set.Icc (0 : ℝ) (1 / 2),
      |deriv (fun value : ℝ => (1 - value) ^ exponent) scale + exponent| ≤
        constant * scale := by
  obtain ⟨constant, hpositive, hbound⟩ := exists_rpow_linear_difference_bound (exponent - 1)
  refine ⟨|exponent| * constant + 1, by positivity, ?_⟩
  intro scale hscale
  have hbase : 1 - scale ≠ 0 := by linarith [hscale.2]
  have hd := (((hasDerivAt_const scale (1 : ℝ)).sub (hasDerivAt_id scale)).rpow_const
    (p := exponent) (Or.inl hbase)).deriv
  have hd' : deriv (fun value : ℝ => (1 - value) ^ exponent) scale =
      (0 - 1) * exponent * (1 - scale) ^ (exponent - 1) := by
    simpa only [Pi.sub_apply, id_eq] using! hd
  rw [hd']
  have heq : (0 - 1) * exponent * (1 - scale) ^ (exponent - 1) + exponent =
      -exponent * ((1 - scale) ^ (exponent - 1) - 1) := by ring
  rw [heq, abs_mul, abs_neg]
  have h := mul_le_mul_of_nonneg_left (hbound scale hscale) (abs_nonneg exponent)
  nlinarith [hscale.1]

end LambdaCantor


