import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
namespace LambdaCantor.Last

theorem coarse_log_hull_base_lower :
    (45569 / 100000 : ℝ) < -Real.log (317 / 500) := by
  have hseries := Real.sum_range_le_log_div
    (show (0 : ℝ) ≤ 183 / 817 by norm_num)
    (show (183 / 817 : ℝ) < 1 by norm_num) 3
  norm_num [Finset.sum_range_succ] at hseries
  have hidentity : Real.log (500 / 317 : ℝ) = -Real.log (317 / 500 : ℝ) := by
    rw [show (500 / 317 : ℝ) = (317 / 500 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hidentity] at hseries
  linarith

theorem coarse_log_period_base_upper :
    -Real.log (183 / 500 : ℝ) < 10053 / 10000 := by
  have hseries := Real.log_div_le_sum_range_add
    (show (0 : ℝ) ≤ 317 / 683 by norm_num)
    (show (317 / 683 : ℝ) < 1 by norm_num) 8
  norm_num [Finset.sum_range_succ] at hseries
  have hidentity : Real.log (500 / 183 : ℝ) = -Real.log (183 / 500 : ℝ) := by
    rw [show (500 / 183 : ℝ) = (183 / 500 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hidentity] at hseries
  linarith

/-- Explicit bounds for the genuine logarithmic hull and period, obtained
from rational partial sums with rigorous remainder bounds. -/
theorem coarse_log_hull_period_bounds {ratio : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2) :
    45569 / 100000 < -Real.log (1 - ratio) ∧
      -Real.log ratio < 10053 / 10000 ∧
      453 / 1000 < (-Real.log (1 - ratio)) / (-Real.log ratio) ∧
      (-Real.log (1 - ratio)) / (-Real.log ratio) < 1 := by
  have hratio : 0 < ratio := by linarith
  have hless_one : ratio < 1 := by linarith
  have hone : 0 < 1 - ratio := by linarith
  have hhull_compare : Real.log (1 - ratio) ≤ Real.log (317 / 500 : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hone (by norm_num) (by linarith)
  have hperiod_compare : Real.log (183 / 500 : ℝ) ≤ Real.log ratio :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hratio hlower
  have hhull : 45569 / 100000 < -Real.log (1 - ratio) := by
    linarith [coarse_log_hull_base_lower]
  have hperiod : -Real.log ratio < 10053 / 10000 := by
    linarith [coarse_log_period_base_upper]
  have hperiod_positive : 0 < -Real.log ratio := by
    have := Real.log_neg hratio hless_one
    linarith
  have hnormalized_lower : 453 / 1000 < (-Real.log (1 - ratio)) / (-Real.log ratio) := by
    apply (lt_div_iff₀ hperiod_positive).mpr
    nlinarith
  have hnormalized_upper : (-Real.log (1 - ratio)) / (-Real.log ratio) < 1 := by
    apply (div_lt_one hperiod_positive).mpr
    have := Real.strictMonoOn_log hratio hone (show ratio < 1 - ratio by linarith)
    linarith
  exact ⟨hhull, hperiod, hnormalized_lower, hnormalized_upper⟩

end LambdaCantor.Last
