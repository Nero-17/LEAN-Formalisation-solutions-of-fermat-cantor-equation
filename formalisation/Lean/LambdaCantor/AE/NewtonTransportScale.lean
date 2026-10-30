import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace LambdaCantor.AE

theorem newton_normalized_transport_cost
    {cost width constant minimumScale rho lower upper length : ℝ} (depth : ℕ)
    (constant_nonnegative : 0 ≤ constant) (minimum_positive : 0 < minimumScale)
    (rho_positive : 0 < rho) (lower_positive : 0 < lower) (length_nonnegative : 0 ≤ length)
    (cost_bound : cost ≤ constant*rho^2*length*(upper^depth)^2)
    (width_lower : minimumScale*rho*lower^depth ≤ width) :
    cost/width ≤ (constant/minimumScale)*rho*length*(upper^2/lower)^depth := by
  have minimum_width_positive : 0 < minimumScale*rho*lower^depth := by positivity
  have width_positive := minimum_width_positive.trans_le width_lower
  calc
    _ ≤ (constant*rho^2*length*(upper^depth)^2)/width :=
      div_le_div_of_nonneg_right cost_bound width_positive.le
    _ ≤ (constant*rho^2*length*(upper^depth)^2)/(minimumScale*rho*lower^depth) :=
      div_le_div_of_nonneg_left (by positivity) minimum_width_positive width_lower
    _ = _ := by
      rw [div_pow, show (upper^2)^depth = (upper^depth)^2 by
        rw [← pow_mul, Nat.mul_comm 2 depth, pow_mul]]
      field_simp [minimum_positive.ne', rho_positive.ne', lower_positive.ne']
      <;> ring

end LambdaCantor.AE
