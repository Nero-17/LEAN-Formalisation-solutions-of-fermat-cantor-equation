import LambdaCantor.Last.ExternalKronecker
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

noncomputable section
namespace LambdaCantor.Last
open Filter
open scoped Topology

/-- Irrational rotation gives approximations m-n*k to any real target with
the natural index k arbitrarily large. The integer m is not yet constrained. -/
theorem irrational_integer_difference_approximation {exponent : ℝ}
    (irrational : Irrational exponent) (target : ℝ) {epsilon : ℝ}
    (epsilon_positive : 0 < epsilon) (start : ℕ) :
    ∃ first : ℕ, start ≤ first ∧ ∃ second : ℤ,
      |(second : ℝ)-exponent*first-target| < epsilon := by
  exact ExternalKronecker.forward_integer_difference_approximation
    irrational target epsilon_positive start

/-- Both near-axis depths can be required to be natural and arbitrarily large. -/
theorem irrational_natural_difference_approximation {exponent : ℝ}
    (irrational : Irrational exponent) (exponent_positive : 0 < exponent)
    (target : ℝ) {epsilon : ℝ} (epsilon_positive : 0 < epsilon) (start : ℕ) :
    ∃ first second : ℕ, start ≤ first ∧ start ≤ second ∧
      |(second : ℝ)-exponent*first-target| < epsilon := by
  obtain ⟨cutoff, cutoff_large⟩ := exists_nat_gt (((start : ℝ)-target+epsilon)/exponent)
  obtain ⟨first, first_large, second, approximation⟩ :=
    irrational_integer_difference_approximation irrational target epsilon_positive (max start cutoff)
  have cutoff_le_first : (cutoff : ℝ) ≤ first := by
    exact_mod_cast (le_trans (le_max_right start cutoff) first_large)
  have cutoff_product : (start : ℝ)-target+epsilon < exponent*cutoff := by
    have inequality := (div_lt_iff₀ exponent_positive).mp cutoff_large
    simpa only [mul_comm] using inequality
  have approximation_bounds := abs_lt.mp approximation
  have second_large : (start : ℝ) < second := by
    nlinarith [mul_le_mul_of_nonneg_left cutoff_le_first exponent_positive.le]
  have second_nonnegative : (0 : ℤ) ≤ second := by
    have : (0 : ℝ) ≤ second := by
      linarith [(Nat.cast_nonneg start : (0 : ℝ) ≤ (start : ℝ))]
    exact_mod_cast this
  have second_cast : ((second.toNat : ℕ) : ℝ) = (second : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg second_nonnegative)
  refine ⟨first, second.toNat, (le_max_left start cutoff).trans first_large, ?_, ?_⟩
  · have bound : (start : ℝ) ≤ (second.toNat : ℝ) := by
      rw [second_cast]
      exact second_large.le
    exact_mod_cast bound
  · simpa only [second_cast] using approximation

/-- Irrationality supplies two escaping natural depth sequences whose phase
converges to any prescribed real value. -/
theorem irrational_depth_sequences {exponent : ℝ}
    (irrational : Irrational exponent) (exponent_positive : 0 < exponent)
    (target : ℝ) :
    ∃ first second : ℕ → ℕ,
      Tendsto first atTop atTop ∧ Tendsto second atTop atTop ∧
      Tendsto (fun index => (second index : ℝ)-exponent*first index)
        atTop (𝓝 target) := by
  have approximations : ∀ index : ℕ, ∃ first second : ℕ,
      index ≤ first ∧ index ≤ second ∧
      |(second : ℝ)-exponent*first-target| < 1/((index : ℝ)+1) := by
    intro index
    exact irrational_natural_difference_approximation irrational exponent_positive target
      (by positivity) index
  choose first second first_large second_large approximation using approximations
  refine ⟨first, second, tendsto_atTop_mono first_large tendsto_id,
    tendsto_atTop_mono second_large tendsto_id, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun _ => abs_nonneg _) (fun index => (approximation index).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- The near-axis coefficient can converge to any positive prescribed value.
Both cylinder depths tend to infinity at the same time. -/
theorem irrational_coefficient_sequences {exponent ratio coefficient : ℝ}
    (irrational : Irrational exponent) (exponent_positive : 0 < exponent)
    (ratio_positive : 0 < ratio) (ratio_less_one : ratio < 1)
    (coefficient_positive : 0 < coefficient) :
    ∃ first second : ℕ → ℕ,
      Tendsto first atTop atTop ∧ Tendsto second atTop atTop ∧
      Tendsto (fun index => exponent * ratio ^
        ((second index : ℝ)-exponent*first index)) atTop (𝓝 coefficient) := by
  obtain ⟨first, second, first_tendsto, second_tendsto, phase_tendsto⟩ :=
    irrational_depth_sequences irrational exponent_positive
      (Real.log (coefficient/exponent)/Real.log ratio)
  have logarithm_nonzero : Real.log ratio ≠ 0 :=
    ne_of_lt (Real.log_neg ratio_positive ratio_less_one)
  have limit_value : exponent * ratio ^
      (Real.log (coefficient/exponent)/Real.log ratio) = coefficient := by
    rw [Real.rpow_def_of_pos ratio_positive, mul_div_cancel₀ _ logarithm_nonzero,
      Real.exp_log (div_pos coefficient_positive exponent_positive)]
    exact mul_div_cancel₀ coefficient exponent_positive.ne'
  refine ⟨first, second, first_tendsto, second_tendsto, ?_⟩
  rw [← limit_value]
  exact tendsto_const_nhds.mul
    ((Real.continuous_const_rpow ratio_positive.ne').continuousAt.tendsto.comp phase_tendsto)
/-- The irrational coefficient sequence in the exact algebraic form used
by the actual normalized source and its Cantor embedding. -/
theorem irrational_actual_source_sequences {exponent ratio coefficient : ℝ}
    (irrational : Irrational exponent) (exponent_positive : 0 < exponent)
    (ratio_positive : 0 < ratio) (ratio_less_one : ratio < 1)
    (coefficient_positive : 0 < coefficient) :
    ∃ first second : ℕ → ℕ,
      Tendsto (fun index => ratio^(second index)) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun index => exponent*ratio^(second index)/(ratio^(first index))^exponent)
        atTop (𝓝 coefficient) := by
  obtain ⟨first, second, first_tendsto, second_tendsto, coefficient_tendsto⟩ :=
    irrational_coefficient_sequences irrational exponent_positive ratio_positive ratio_less_one
      coefficient_positive
  refine ⟨first, second,
    (tendsto_pow_atTop_nhds_zero_of_lt_one ratio_positive.le ratio_less_one).comp second_tendsto, ?_⟩
  convert coefficient_tendsto using 1
  funext index
  rw [Real.rpow_sub ratio_positive, Real.rpow_natCast,
    show exponent*(first index : ℝ) = (first index : ℝ)*exponent by ring,
    Real.rpow_mul ratio_positive.le, Real.rpow_natCast]
  exact mul_div_assoc _ _ _
end LambdaCantor.Last


