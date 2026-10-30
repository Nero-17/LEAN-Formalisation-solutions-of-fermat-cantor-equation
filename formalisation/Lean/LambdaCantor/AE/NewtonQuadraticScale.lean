import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace LambdaCantor.AE

theorem newton_quadratic_scale_bound
    {tailBound mixedBound secondBound displacementConstant rho power length displacement denominator slope : ℝ}
    (tail_nonnegative : 0 ≤ tailBound) (mixed_nonnegative : 0 ≤ mixedBound) (second_nonnegative : 0 ≤ secondBound)
    (displacement_constant_nonnegative : 0 ≤ displacementConstant) (rho_nonnegative : 0 ≤ rho)
    (power_nonnegative : 0 ≤ power) (length_ge_one : 1 ≤ length) (displacement_nonnegative : 0 ≤ displacement)
    (displacement_bound : displacement ≤ displacementConstant*rho*power)
    (slope_positive : 0 < slope) (denominator_lower : slope ≤ denominator) :
    (tailBound*rho^2*power^2+mixedBound*rho*length*power*displacement+secondBound*displacement^2)/denominator ≤
      ((tailBound+mixedBound*displacementConstant+secondBound*displacementConstant^2)/slope)*rho^2*length*power^2 := by
  have denominator_positive := slope_positive.trans_le denominator_lower
  have length_nonnegative : 0 ≤ length := by linarith
  have displacement_square := pow_le_pow_left₀ displacement_nonnegative displacement_bound 2
  have numerator_bound :
      tailBound*rho^2*power^2+mixedBound*rho*length*power*displacement+secondBound*displacement^2 ≤
      (tailBound+mixedBound*displacementConstant+secondBound*displacementConstant^2)*rho^2*length*power^2 := by
    calc
      _ ≤ tailBound*rho^2*power^2+mixedBound*rho*length*power*(displacementConstant*rho*power)+
          secondBound*(displacementConstant*rho*power)^2 :=
        add_le_add
          (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left displacement_bound
            (show 0 ≤ mixedBound*rho*length*power by positivity)))
          (mul_le_mul_of_nonneg_left displacement_square second_nonnegative)
      _ = (tailBound+mixedBound*displacementConstant*length+secondBound*displacementConstant^2)*rho^2*power^2 := by ring
      _ ≤ (tailBound+mixedBound*displacementConstant+secondBound*displacementConstant^2)*length*rho^2*power^2 := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right _ (sq_nonneg rho)) (sq_nonneg power)
        have tail_term := le_mul_of_one_le_right tail_nonnegative length_ge_one
        have second_term := le_mul_of_one_le_right
          (mul_nonneg second_nonnegative (sq_nonneg displacementConstant)) length_ge_one
        nlinarith
      _ = _ := by ring
  calc
    _ ≤ ((tailBound+mixedBound*displacementConstant+secondBound*displacementConstant^2)*rho^2*length*power^2)/denominator :=
      div_le_div_of_nonneg_right numerator_bound denominator_positive.le
    _ ≤ ((tailBound+mixedBound*displacementConstant+secondBound*displacementConstant^2)*rho^2*length*power^2)/slope :=
      div_le_div_of_nonneg_left (by positivity) slope_positive denominator_lower
    _ = _ := by ring

end LambdaCantor.AE
