import LambdaCantor.AE.CenteredResidual
import LambdaCantor.AE.CenteredDisplacementSecond

noncomputable section

namespace LambdaCantor.AE

def centeredHorizontalFirst (tailDepth : ℕ) (digits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  -(tailDepth : ℝ)*ratio^(tailDepth-1) - centeredDisplacementFirst 0 tailDepth digits ratio

def centeredHorizontalSecond (tailDepth : ℕ) (digits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  -(tailDepth : ℝ)*((tailDepth-1 : ℕ) : ℝ)*ratio^(tailDepth-1-1) -
    centeredDisplacementSecond 0 tailDepth digits ratio

theorem centeredTailFactor_first_actual (tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1) :
    HasDerivAt (centeredTailFactor tailDepth digits)
      (centeredDisplacementFirst 0 tailDepth digits ratio) ratio := by
  convert centeredDisplacement_first_actual 0 tailDepth digits positive less_one using 1
  funext parameter
  simp only [centeredTailFactor, centeredAddressDisplacement, pow_zero, one_mul]

theorem centeredHorizontalFactor_first_actual (tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1) :
    HasDerivAt (centeredHorizontalFactor tailDepth digits)
      (centeredHorizontalFirst tailDepth digits ratio) ratio := by
  have model := ((hasDerivAt_pow tailDepth ratio).const_sub 2).sub
    (centeredTailFactor_first_actual tailDepth digits positive less_one)
  have hfunction := model.congr_of_eventuallyEq
    (f₁ := centeredHorizontalFactor tailDepth digits)
    (Filter.Eventually.of_forall (fun parameter => by
      simp only [centeredHorizontalFactor, centeredTailFactor, Pi.sub_apply]
      ring))
  apply hfunction.congr_deriv
  unfold centeredHorizontalFirst
  ring

theorem centeredHorizontalFactor_second_actual (tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1) :
    HasDerivAt (centeredHorizontalFirst tailDepth digits)
      (centeredHorizontalSecond tailDepth digits ratio) ratio := by
  have polynomial := (hasDerivAt_pow (tailDepth-1) ratio).const_mul (-(tailDepth : ℝ))
  have tail := centeredDisplacement_second_actual 0 tailDepth digits positive less_one
  have hfunction := (polynomial.sub tail).congr_of_eventuallyEq
    (f₁ := centeredHorizontalFirst tailDepth digits)
    (Filter.Eventually.of_forall (fun _ => rfl))
  apply hfunction.congr_deriv
  unfold centeredHorizontalSecond
  ring

/-- Explicit second derivative bound for the full horizontal factor, rather
than only for the nonlinear vertical Taylor remainder. -/
theorem centeredHorizontalSecond_bound
    (tailDepth : ℕ) (digits : ℕ → Bool) {ratio firstBound secondBound : ℝ}
    (positive : 0 < ratio) (less_one : ratio < 1)
    (first_bound : |deriv (fun parameter => address parameter digits) ratio| ≤ firstBound)
    (second_bound : |deriv (deriv (fun parameter => address parameter digits)) ratio| ≤ secondBound) :
    |centeredHorizontalSecond tailDepth digits ratio| ≤
      2*(tailDepth : ℝ)*((tailDepth-1 : ℕ) : ℝ)*ratio^(tailDepth-1-1) +
        2*(tailDepth : ℝ)*ratio^(tailDepth-1)*firstBound + ratio^tailDepth*secondBound := by
  have tail_bound := centeredDisplacement_second_bound 0 tailDepth digits positive less_one first_bound second_bound
  simp only [Nat.cast_zero, zero_mul, Nat.zero_add, zero_add] at tail_bound
  unfold centeredHorizontalSecond
  have triangle := abs_sub
    (-(tailDepth : ℝ)*((tailDepth-1 : ℕ) : ℝ)*ratio^(tailDepth-1-1))
    (centeredDisplacementSecond 0 tailDepth digits ratio)
  have polynomial_absolute :
      |-(tailDepth : ℝ)*((tailDepth-1 : ℕ) : ℝ)*ratio^(tailDepth-1-1)| =
        (tailDepth : ℝ)*((tailDepth-1 : ℕ) : ℝ)*ratio^(tailDepth-1-1) := by
    rw [neg_mul, neg_mul, abs_neg, abs_of_nonneg (by positivity)]
  rw [polynomial_absolute] at triangle
  nlinarith

/-- Uniform polynomial/exponential majorant for both complete factor second
derivatives on a fixed compact parameter band. -/
theorem centeredFactorSecond_uniform_bound
    (tailDepth : ℕ) (large : 2 ≤ tailDepth) (digits : ℕ → Bool)
    {lower ratio upper firstBound secondBound : ℝ}
    (lower_positive : 0 < lower) (ratio_lower : lower ≤ ratio) (ratio_upper : ratio ≤ upper) (upper_less_one : upper < 1)
    (first_bound : |deriv (fun parameter => address parameter digits) ratio| ≤ firstBound)
    (second_bound : |deriv (deriv (fun parameter => address parameter digits)) ratio| ≤ secondBound) :
    |centeredHorizontalSecond tailDepth digits ratio| ≤
        (2/lower^2+2*firstBound/lower+secondBound)*(tailDepth : ℝ)^2*upper^tailDepth ∧
      |centeredDisplacementSecond 0 tailDepth digits ratio| ≤
        (2/lower^2+2*firstBound/lower+secondBound)*(tailDepth : ℝ)^2*upper^tailDepth := by
  have positive := lower_positive.trans_le ratio_lower
  have less_one := ratio_upper.trans_lt upper_less_one
  have first_nonnegative := (abs_nonneg _).trans first_bound
  have second_nonnegative := (abs_nonneg _).trans second_bound
  have depth_ge_two : (2 : ℝ) ≤ tailDepth := by exact_mod_cast large
  have depth_ge_one : (1 : ℝ) ≤ tailDepth := by linarith
  have square_ge_one : (1 : ℝ) ≤ (tailDepth : ℝ)^2 := by nlinarith
  have depth_le_square : (tailDepth : ℝ) ≤ (tailDepth : ℝ)^2 := by nlinarith
  have predecessor_bound : ((tailDepth-1 : ℕ) : ℝ) ≤ tailDepth := by exact_mod_cast Nat.sub_le tailDepth 1
  have shift_two := centered_shifted_power_bound lower_positive ratio_lower ratio_upper tailDepth 2 large
  have shift_one := centered_shifted_power_bound lower_positive ratio_lower ratio_upper tailDepth 1 (by omega)
  simp only [pow_one] at shift_one
  have power_bound := pow_le_pow_left₀ positive.le ratio_upper tailDepth
  have coefficient_bound : 2*(tailDepth : ℝ)*((tailDepth-1 : ℕ) : ℝ) ≤ 2*(tailDepth : ℝ)^2 := by
    nlinarith [mul_le_mul_of_nonneg_left predecessor_bound (Nat.cast_nonneg tailDepth)]
  have first_term := mul_le_mul coefficient_bound shift_two
    (pow_nonneg positive.le (tailDepth-2)) (by positivity : 0 ≤ 2*(tailDepth : ℝ)^2)
  have second_term := mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left depth_le_square (by norm_num : (0 : ℝ) ≤ 2)) shift_one
      (pow_nonneg positive.le (tailDepth-1)) (by positivity : 0 ≤ 2*(tailDepth : ℝ)^2)) first_nonnegative
  have third_term : ratio^tailDepth*secondBound ≤ (tailDepth : ℝ)^2*upper^tailDepth*secondBound := by
    apply (mul_le_mul_of_nonneg_right power_bound second_nonnegative).trans
    have nonnegative : 0 ≤ upper^tailDepth*secondBound := by
      exact mul_nonneg (pow_nonneg (positive.le.trans ratio_upper) _) second_nonnegative
    simpa only [mul_assoc] using le_mul_of_one_le_left nonnegative square_ge_one
  have majorant :
      2*(tailDepth : ℝ)*((tailDepth-1 : ℕ) : ℝ)*ratio^(tailDepth-1-1) +
          2*(tailDepth : ℝ)*ratio^(tailDepth-1)*firstBound+ratio^tailDepth*secondBound ≤
        (2/lower^2+2*firstBound/lower+secondBound)*(tailDepth : ℝ)^2*upper^tailDepth := by
    simp only [Nat.sub_sub] at first_term ⊢
    apply (add_le_add (add_le_add first_term second_term) third_term).trans_eq
    ring
  have horizontal := centeredHorizontalSecond_bound tailDepth digits positive less_one first_bound second_bound
  have tail := centeredDisplacement_second_bound 0 tailDepth digits positive less_one first_bound second_bound
  simp only [Nat.cast_zero, zero_mul, Nat.zero_add, zero_add] at tail
  refine ⟨horizontal.trans majorant, le_trans ?_ majorant⟩
  have polynomial_nonnegative : 0 ≤
      (tailDepth : ℝ)*((tailDepth-1 : ℕ) : ℝ)*ratio^(tailDepth-1-1) := by positivity
  nlinarith

end LambdaCantor.AE
