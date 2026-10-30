import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace LambdaCantor.Integer

/-- Finite rational-operation lower bound; rational input gives a rational value. -/
noncomputable def logSeriesLower (x : ℝ) (terms : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range terms,
    ((x-1)/(x+1))^(2*i+1) / (2*i+1)

/-- A deliberately conservative rational tail bound. It follows from existing
mathlib logarithm-series estimates and does not assume a transcendental oracle.
It is weaker than the paper's bound with an additional factor 2*terms+1 in the
denominator, so numerical certificates must be checked with this bound anew. -/
noncomputable def logSeriesUpper (x : ℝ) (terms : ℕ) : ℝ :=
  logSeriesLower x terms +
    2 * ((x-1)/(x+1))^(2*terms+1) / (1-((x-1)/(x+1))^2)

theorem log_series_bounds (x : ℝ) (positive : 1 ≤ x) (terms : ℕ) :
    logSeriesLower x terms ≤ Real.log x ∧
      Real.log x ≤ logSeriesUpper x terms := by
  have denominator : 0 < x+1 := by linarith
  have parameterNonnegative : 0 ≤ (x-1)/(x+1) :=
    div_nonneg (by linarith) denominator.le
  have parameterLess : (x-1)/(x+1) < 1 := by
    apply (div_lt_one denominator).2
    linarith
  have identity : (1+(x-1)/(x+1))/(1-(x-1)/(x+1)) = x := by
    have nonzero : 1-(x-1)/(x+1) ≠ 0 := by linarith
    apply (div_eq_iff nonzero).2
    field_simp [ne_of_gt denominator]
    <;> ring
  have lower := Real.sum_range_le_log_div parameterNonnegative parameterLess terms
  have upper := Real.log_div_le_sum_range_add parameterNonnegative parameterLess terms
  rw [identity] at lower upper
  constructor
  · unfold logSeriesLower
    linarith
  · unfold logSeriesUpper logSeriesLower
    convert! mul_le_mul_of_nonneg_left upper (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring

end LambdaCantor.Integer
