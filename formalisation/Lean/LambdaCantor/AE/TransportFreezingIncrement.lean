import LambdaCantor.AE.MixtureFreezingFactor
import Mathlib.Tactic.GCongr

noncomputable section

namespace LambdaCantor.AE

/-- The averaged squared amplitude and actual normalized transport cost
produce exactly the summable freezing ratio, with only a linear initial and
prefix depth factor. No analytic increment estimate is assumed here. -/
theorem transport_freezing_increment_bound
    {lower upper regularity constant energyConstant costConstant rho averageEnergy cost : ℝ}
    (shift depth : ℕ) (lower_positive : 0 < lower) (upper_positive : 0 < upper)
    (regularity_positive : 0 < regularity) (constant_nonnegative : 0 ≤ constant)
    (energyConstant_nonnegative : 0 ≤ energyConstant) (costConstant_nonnegative : 0 ≤ costConstant)
    (rho_nonnegative : 0 ≤ rho) (average_nonnegative : 0 ≤ averageEnergy) (cost_nonnegative : 0 ≤ cost)
    (energy_bound : averageEnergy ≤ energyConstant*
      upper^(-(depth : ℝ)*(1-Real.log 2/Real.log (1/lower))))
    (cost_bound : cost ≤ costConstant*rho*(((shift+depth+1 : ℕ) : ℝ))*(upper^2/lower)^depth) :
    constant*averageEnergy^(1/(2*(1+regularity)))*cost^(regularity/(1+regularity)) ≤
      (constant*energyConstant^(1/(2*(1+regularity)))*costConstant^(regularity/(1+regularity)))*
        rho^(regularity/(1+regularity))*(((shift+depth+1 : ℕ) : ℝ))*freezingRatio lower upper regularity^depth := by
  have denominator_positive : 0 < 1+regularity := by positivity
  have ratio_nonnegative : 0 ≤ freezingRatio lower upper regularity := by
    unfold freezingRatio
    positivity
  have energy_exponent_nonnegative : 0 ≤ 1/(2*(1+regularity)) := by positivity
  have cost_exponent_nonnegative : 0 ≤ regularity/(1+regularity) := by positivity
  have cost_exponent_le_one : regularity/(1+regularity) ≤ 1 := by
    apply (div_le_one denominator_positive).mpr
    linarith
  have depth_ge_one : (1 : ℝ) ≤ ((shift+depth+1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (shift+depth))
  have depth_power := Real.rpow_le_self_of_one_le depth_ge_one cost_exponent_le_one
  have energy_power := Real.rpow_le_rpow average_nonnegative energy_bound energy_exponent_nonnegative
  have cost_power := Real.rpow_le_rpow cost_nonnegative cost_bound cost_exponent_nonnegative
  calc
    _ ≤ constant*(energyConstant*upper^(-(depth : ℝ)*(1-Real.log 2/Real.log (1/lower))))^
          (1/(2*(1+regularity)))*
        (costConstant*rho*(((shift+depth+1 : ℕ) : ℝ))*(upper^2/lower)^depth)^(regularity/(1+regularity)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left energy_power constant_nonnegative) cost_power
        (Real.rpow_nonneg cost_nonnegative _) (by positivity)
    _ = (constant*energyConstant^(1/(2*(1+regularity)))*costConstant^(regularity/(1+regularity)))*
        rho^(regularity/(1+regularity))*(((shift+depth+1 : ℕ) : ℝ))^(regularity/(1+regularity))*
          freezingRatio lower upper regularity^depth := by
      rw [Real.mul_rpow energyConstant_nonnegative (by positivity),
        Real.mul_rpow (show 0 ≤ costConstant*rho*(((shift+depth+1 : ℕ) : ℝ)) by positivity) (by positivity),
        Real.mul_rpow (mul_nonneg costConstant_nonnegative rho_nonnegative) (by positivity),
        Real.mul_rpow costConstant_nonnegative rho_nonnegative]
      have identity := averaged_transport_freezing_factor depth lower_positive upper_positive regularity_positive
      calc
        _ = (constant*energyConstant^(1/(2*(1+regularity)))*costConstant^(regularity/(1+regularity)))*
          rho^(regularity/(1+regularity))*(((shift+depth+1 : ℕ) : ℝ))^(regularity/(1+regularity))*
          (upper^(-(depth : ℝ)*(1-Real.log 2/Real.log (1/lower))))^(1/(2*(1+regularity)))*
            (((upper^2/lower)^depth)^(regularity/(1+regularity))) := by ring
        _ = _ := by rw [mul_assoc, identity]
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left depth_power (by positivity)) (by positivity)

end LambdaCantor.AE
