import LambdaCantor.AE.CenteredSmallBallIntervals
import LambdaCantor.AE.CenteredPrefixWindow

noncomputable section
open Set MeasureTheory
namespace LambdaCantor.AE

/-- Small-ball estimate for the actual centred root family, under the explicit
root-existence and derivative bounds supplied by the centred analytic construction.
The probability and first-tail geometric arguments are proved internally. -/
theorem centered_root_interval_smallBall
    {exponent lower upper windowLower windowUpper rho derivativeBound left right : ℝ}
    (exponent_ge_one : 1 ≤ exponent) (lower_positive : 0 < lower) (upper_half : upper < 1/2)
    (window_lower : lower ≤ windowLower) (window_upper : windowUpper ≤ upper)
    (rho_positive : 0 < rho) (derivative_positive : 0 < derivativeBound)
    (horizontalDepth verticalDepth tailDepth : ℕ)
    (root : (ℕ → Bool × Bool) → ℝ) (root_measurable : Measurable root)
    (root_mem : ∀ digits, root digits ∈ Icc windowLower windowUpper)
    (root_zero : ∀ digits, centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits (root digits) = 0)
    (root_power_lower : ∀ digits, rho/2 ≤ (root digits)^tailDepth)
    (root_power_small : ∀ digits, (root digits)^tailDepth ≤ 1/2)
    (differentiable : ∀ digits ratio, ratio ∈ Icc windowLower windowUpper →
      DifferentiableAt ℝ (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) ratio)
    (derivative_bound : ∀ digits ratio, ratio ∈ Icc windowLower windowUpper →
      |deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) ratio| ≤ derivativeBound)
    (ordered : left ≤ right) :
    First.Roots.rootLaw root (Icc left right) ≤
      ENNReal.ofReal
        (((4*derivativeBound)/((exponent*(1/2:ℝ)^(exponent-1))*(1-2*upper)*lower))^
            (Real.log (1/2)/Real.log lower) *
          ((right-left)/rho)^(Real.log (1/2)/Real.log lower)) := by
  have exponent_positive : 0 < exponent := by linarith
  have gap_positive : 0 < 1-2*upper := by linarith
  have power_positive : 0 < (1/2:ℝ)^(exponent-1) := Real.rpow_pos_of_pos (by norm_num) _
  have lower_less_one : lower < 1 := by
    have band := root_mem (fun _ => (false, false))
    linarith [band.1, band.2]
  have separation_positive :
      0 < (exponent*(1/2:ℝ)^(exponent-1))*(rho/2)*(1-2*upper)/derivativeBound := by
    have exponent_positive : 0 < exponent := by linarith
    have gap_positive : 0 < 1-2*upper := by linarith
    positivity
  have bound := rootLaw_interval_bound_of_first_coordinate_separation root root_measurable
    lower_positive lower_less_one separation_positive
    (Last.binary_exponent_positive lower_positive lower_less_one)
    (Last.binary_exponent_rpow lower_positive lower_less_one)
    (centered_root_first_coordinate_separation_on_window exponent_ge_one lower_positive upper_half window_lower window_upper rho_positive
      derivative_positive horizontalDepth verticalDepth tailDepth root root_mem root_zero root_power_lower
      root_power_small differentiable derivative_bound)
    ordered
  have coefficient_nonnegative : 0 ≤
      (4*derivativeBound)/((exponent*(1/2:ℝ)^(exponent-1))*(1-2*upper)*lower) := by
    have gap_positive : 0 < 1-2*upper := by linarith
    positivity
  have algebra :
      2*(right-left)/(((exponent*(1/2:ℝ)^(exponent-1))*(rho/2)*(1-2*upper)/derivativeBound)*lower) =
      ((4*derivativeBound)/((exponent*(1/2:ℝ)^(exponent-1))*(1-2*upper)*lower))*((right-left)/rho) := by
    field_simp [rho_positive.ne', derivative_positive.ne', lower_positive.ne',
      exponent_positive.ne', gap_positive.ne', power_positive.ne']
    <;> ring
  rw [algebra, Real.mul_rpow coefficient_nonnegative (div_nonneg (sub_nonneg.mpr ordered) rho_positive.le)] at bound
  exact bound

end LambdaCantor.AE


