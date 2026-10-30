import LambdaCantor.Classical.GeneralCover
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
namespace LambdaCantor.Integer.Exceptional

def powerRemainder (exponent : ℕ) (base value : ℝ) : ℝ :=
  (base+value)^exponent - base^exponent - exponent*base^(exponent-1)*value

theorem powerRemainder_zero (exponent : ℕ) (base : ℝ) : powerRemainder exponent base 0 = 0 := by
  simp [powerRemainder]

theorem powerRemainder_derivative (exponent : ℕ) (base value : ℝ) :
    HasDerivAt (powerRemainder exponent base)
      (exponent*((base+value)^(exponent-1)-base^(exponent-1))) value := by
  have power := ((hasDerivAt_id value).const_add base).pow exponent
  have linear := (hasDerivAt_id value).const_mul ((exponent : ℝ)*base^(exponent-1))
  have combined := (power.sub_const (base^exponent)).sub linear
  convert! combined using 1 <;>
    simp only [powerRemainder,Pi.sub_apply,Pi.pow_apply,id_eq,mul_one] <;> ring

theorem powerRemainder_increment (exponent : ℕ) (base : ℝ) (base_nonnegative : 0 ≤ base)
    (first second : ℝ) (first_bounds : first ∈ Set.Icc (0 : ℝ) 1)
    (second_bounds : second ∈ Set.Icc (0 : ℝ) 1) (ordered : first ≤ second) :
    0 ≤ powerRemainder exponent base second - powerRemainder exponent base first ∧
    powerRemainder exponent base second - powerRemainder exponent base first ≤
      exponent*((base+1)^(exponent-1)-base^(exponent-1))*(second-first) := by
  have estimate := Classical.increment_bounds_of_deriv (powerRemainder exponent base) 0
    (exponent*((base+1)^(exponent-1)-base^(exponent-1)))
    (fun value _ => (powerRemainder_derivative exponent base value).continuousAt.continuousWithinAt)
    (fun value _ => (powerRemainder_derivative exponent base value).differentiableAt.differentiableWithinAt)
    (fun value membership => by
      rw [(powerRemainder_derivative exponent base value).deriv]
      have lower := pow_le_pow_left₀ base_nonnegative
        (by linarith [membership.1] : base ≤ base+value) (exponent-1)
      have upper := pow_le_pow_left₀ (by linarith [membership.1] : 0 ≤ base+value)
        (by linarith [membership.2] : base+value ≤ base+1) (exponent-1)
      constructor
      · exact mul_nonneg (Nat.cast_nonneg exponent) (sub_nonneg.mpr lower)
      · exact mul_le_mul_of_nonneg_left (sub_le_sub_right upper _) (Nat.cast_nonneg exponent))
    first second first_bounds second_bounds ordered
  simpa only [zero_mul] using estimate

/-- Mean-value bound for the nonlinear part of an arbitrary integer power.
No polynomial-specific error estimate is assumed. -/
theorem powerRemainder_difference (exponent : ℕ) (base : ℝ) (base_nonnegative : 0 ≤ base)
    (first second : ℝ) (first_bounds : first ∈ Set.Icc (0 : ℝ) 1)
    (second_bounds : second ∈ Set.Icc (0 : ℝ) 1) :
    |powerRemainder exponent base first - powerRemainder exponent base second| ≤
      exponent*((base+1)^(exponent-1)-base^(exponent-1))*|first-second| := by
  rcases le_total first second with ordered | ordered
  · have estimate := powerRemainder_increment exponent base base_nonnegative first second
      first_bounds second_bounds ordered
    rw [abs_of_nonpos (by linarith [estimate.1]), abs_of_nonpos (sub_nonpos.mpr ordered)]
    nlinarith [estimate.2]
  · have estimate := powerRemainder_increment exponent base base_nonnegative second first
      second_bounds first_bounds ordered
    rw [abs_of_nonneg (sub_nonneg.mpr (by linarith [estimate.1])),
      abs_of_nonneg (sub_nonneg.mpr ordered)]
    exact estimate.2

theorem normalized_powerRemainder_difference (exponent : ℕ) (base denominator : ℝ)
    (base_nonnegative : 0 ≤ base) (denominator_positive : 0 < denominator)
    (first second : ℝ) (first_bounds : first ∈ Set.Icc (0 : ℝ) 1)
    (second_bounds : second ∈ Set.Icc (0 : ℝ) 1) :
    |powerRemainder exponent base first / denominator -
        powerRemainder exponent base second / denominator| ≤
      (exponent*((base+1)^(exponent-1)-base^(exponent-1))/denominator)*|first-second| := by
  rw [← sub_div, abs_div, abs_of_pos denominator_positive]
  have estimate := div_le_div_of_nonneg_right
    (powerRemainder_difference exponent base base_nonnegative first second first_bounds second_bounds)
    denominator_positive.le
  simpa only [mul_div_right_comm] using estimate

end LambdaCantor.Integer.Exceptional
