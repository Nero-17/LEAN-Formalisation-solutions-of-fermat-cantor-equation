import LambdaCantor.Last.RationalLastStrict
import LambdaCantor.Last.AnalyticCoarseConclusion

noncomputable section
namespace LambdaCantor.Last

theorem rational_lastTransition_lt_critical
    {numerator denominator : ℕ} (numerator_large : 4 ≤ numerator)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    (exponent_gt_one : denominator < numerator) :
    lastTransition ((numerator : ℝ) / denominator) < (Real.sqrt 3 - 1) / 2 := by
  apply rational_lastTransition_lt_critical_of_infinite_intersections
    numerator_large denominator_positive coprime exponent_gt_one
  intro ratio hlower hupper
  have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hnonnegative := Real.sqrt_nonneg (3 : ℝ)
  have hdenominator : (0 : ℝ) < denominator := by exact_mod_cast denominator_positive
  have hexponent : 1 < (numerator : ℝ) / denominator :=
    (one_lt_div hdenominator).mpr (by exact_mod_cast exponent_gt_one)
  apply coarse_rational_infinite_intersection (by nlinarith) hupper hexponent
    (show 0 < numerator by omega) denominator_positive
  exact div_mul_cancel₀ _ hdenominator.ne'

end LambdaCantor.Last
