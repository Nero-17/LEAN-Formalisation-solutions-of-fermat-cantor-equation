import Mathlib.Tactic.Positivity
import LambdaCantor.Common
import LambdaCantor.First.RationalLimit

noncomputable section
open Set Filter Topology
namespace LambdaCantor.First

/-- The frozen punctured-limit theorem follows from exactly the three
preceding onset inputs. These geometric inputs are explicit hypotheses,
not axioms or claims that their proofs have been completed. -/
theorem first_punctured_limit_of_onset_bounds
    (hlower : ∀ exponent : ℝ, 2 ≤ exponent → 1 / 4 ≤ firstTransition exponent)
    (hirrational : ∀ exponent : ℝ, 2 ≤ exponent →
      (∀ q : ℚ, exponent ≠ (q : ℝ)) → firstTransition exponent = 1 / 4)
    (hrational : ∀ q : ℚ, 2 ≤ (q : ℝ) →
      firstTransition q - 1 / 4 ≤
        (3 / 2 : ℝ) ^ (q : ℝ) * Real.log 4 / (2 * (q : ℝ) * q.den))
    (center : ℝ) :
    Tendsto firstTransition
      (𝓝[{exponent : ℝ | 2 ≤ exponent ∧ exponent ≠ center}] center)
      (𝓝 (1 / 4)) := by
  apply punctured_limit_of_denominator_bound firstTransition (1 / 4) center
    ((3 / 2 : ℝ) ^ (center + 1) * Real.log 4 / 4) 1 (by norm_num)
    hlower hirrational
  intro q hq hnear
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hpower : (3 / 2 : ℝ) ^ (q : ℝ) ≤ (3 / 2 : ℝ) ^ (center + 1) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have := (abs_lt.mp hnear).2
    linarith
  have hlog : 0 ≤ Real.log 4 := (Real.log_pos (by norm_num)).le
  have hnum : 0 ≤ (3 / 2 : ℝ) ^ (center + 1) * Real.log 4 := by positivity
  calc
    firstTransition q - 1 / 4 ≤
        (3 / 2 : ℝ) ^ (q : ℝ) * Real.log 4 / (2 * (q : ℝ) * q.den) := hrational q hq
    _ ≤ (3 / 2 : ℝ) ^ (center + 1) * Real.log 4 / (2 * (q : ℝ) * q.den) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpower hlog) (by positivity)
    _ ≤ (3 / 2 : ℝ) ^ (center + 1) * Real.log 4 / (4 * q.den) :=
      div_le_div_of_nonneg_left hnum (by positivity) (by nlinarith)
    _ = ((3 / 2 : ℝ) ^ (center + 1) * Real.log 4 / 4) / q.den := by ring

end LambdaCantor.First

