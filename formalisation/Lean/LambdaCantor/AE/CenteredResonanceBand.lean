import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace LambdaCantor.AE

theorem centered_resonance_two_sided_bound {lower ratio exponentBound discrepancy : ℝ}
    (lower_positive : 0 < lower) (ratio_lower : lower ≤ ratio) (ratio_le_one : ratio ≤ 1)
    (bound_nonnegative : 0 ≤ exponentBound) (discrepancy_bound : |discrepancy| ≤ exponentBound) :
    lower^exponentBound ≤ ratio^discrepancy ∧ ratio^discrepancy ≤ lower^(-exponentBound) := by
  have ratio_positive := lower_positive.trans_le ratio_lower
  have bounds := abs_le.mp discrepancy_bound
  constructor
  · exact (Real.rpow_le_rpow lower_positive.le ratio_lower bound_nonnegative).trans
      (Real.rpow_le_rpow_of_exponent_ge ratio_positive ratio_le_one bounds.2)
  · exact (Real.rpow_le_rpow_of_exponent_ge ratio_positive ratio_le_one bounds.1).trans
      (Real.rpow_le_rpow_of_nonpos lower_positive ratio_lower (neg_nonpos.mpr bound_nonnegative))

theorem centered_phase_absolute_bound {discrepancy target epsilon : ℝ}
    (phase_bound : |discrepancy-target| ≤ epsilon) (epsilon_le_one : epsilon ≤ 1) :
    |discrepancy| ≤ |target|+1 := by
  have triangle := abs_add_le (discrepancy-target) target
  have identity : discrepancy-target+target = discrepancy := by ring
  rw [identity] at triangle
  linarith

end LambdaCantor.AE
