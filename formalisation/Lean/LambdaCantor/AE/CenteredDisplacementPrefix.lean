import LambdaCantor.AE.CenteredDisplacement
import LambdaCantor.First.PrefixEstimates

noncomputable section

namespace LambdaCantor.AE

theorem centeredAddressDisplacement_difference_identity
    (verticalDepth tailDepth : ℕ) (first second : ℕ → Bool) (ratio : ℝ) :
    centeredAddressDisplacement verticalDepth tailDepth first ratio -
      centeredAddressDisplacement verticalDepth tailDepth second ratio =
      -ratio^(verticalDepth+tailDepth) * (address ratio first-address ratio second) := by
  unfold centeredAddressDisplacement
  rw [pow_add]
  ring

theorem centeredAddressDisplacement_shared_prefix_bound
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1)
    (verticalDepth tailDepth depth : ℕ) (first second : ℕ → Bool)
    (agreement : ∀ index < depth, first index = second index) :
    |centeredAddressDisplacement verticalDepth tailDepth first ratio -
      centeredAddressDisplacement verticalDepth tailDepth second ratio| ≤
        ratio^(verticalDepth+tailDepth)*ratio^depth := by
  rw [centeredAddressDisplacement_difference_identity, abs_mul, abs_neg,
    abs_of_nonneg (pow_nonneg positive.le _)]
  exact mul_le_mul_of_nonneg_left
    (address_shared_prefix_bound positive.le less_one first second depth agreement)
    (pow_nonneg positive.le _)

theorem centeredAddressDisplacement_first_difference_identity
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1)
    (verticalDepth tailDepth : ℕ) (first second : ℕ → Bool) :
    deriv (centeredAddressDisplacement verticalDepth tailDepth first) ratio -
      deriv (centeredAddressDisplacement verticalDepth tailDepth second) ratio =
      -(((verticalDepth+tailDepth : ℕ) : ℝ)*ratio^(verticalDepth+tailDepth-1)*
        (address ratio first-address ratio second) +
        ratio^(verticalDepth+tailDepth)*
          (addressParameterDerivative ratio first-addressParameterDerivative ratio second)) := by
  have actual :=
    ((centeredAddressDisplacement_hasDerivAt verticalDepth tailDepth first positive less_one).differentiableAt.hasDerivAt).sub
      ((centeredAddressDisplacement_hasDerivAt verticalDepth tailDepth second positive less_one).differentiableAt.hasDerivAt)
  have factored := ((hasDerivAt_pow (verticalDepth+tailDepth) ratio).mul
    ((hasDerivAt_address_parameter positive less_one first).sub
      (hasDerivAt_address_parameter positive less_one second))).neg
  have same_function :
      (fun parameter => centeredAddressDisplacement verticalDepth tailDepth first parameter -
        centeredAddressDisplacement verticalDepth tailDepth second parameter) =ᶠ[nhds ratio]
      (fun parameter => -(parameter^(verticalDepth+tailDepth)*
        (address parameter first-address parameter second))) := by
    exact Filter.Eventually.of_forall (fun parameter => by
      change centeredAddressDisplacement verticalDepth tailDepth first parameter -
          centeredAddressDisplacement verticalDepth tailDepth second parameter =
        -(parameter^(verticalDepth+tailDepth)*(address parameter first-address parameter second))
      rw [centeredAddressDisplacement_difference_identity]
      ring)
  exact actual.unique (factored.congr_of_eventuallyEq same_function)

/-- Prefix cancellation in the parameter derivative of the genuine vertical
displacement. Every term retains the small factor at depth m+L+j. -/
theorem centeredAddressDisplacement_first_shared_prefix_bound
    {ratio upper : ℝ} (positive : 0 < ratio) (ratio_upper : ratio ≤ upper) (upper_less_one : upper < 1)
    (verticalDepth tailDepth depth : ℕ) (first second : ℕ → Bool)
    (agreement : ∀ index < depth, first index = second index) :
    |deriv (centeredAddressDisplacement verticalDepth tailDepth first) ratio -
      deriv (centeredAddressDisplacement verticalDepth tailDepth second) ratio| ≤
      ((verticalDepth+tailDepth : ℕ) : ℝ)*ratio^(verticalDepth+tailDepth-1)*ratio^depth +
        ratio^(verticalDepth+tailDepth)*
          ((depth : ℝ)*ratio^(depth-1) + 2*addressParameterDerivativeBound upper*ratio^depth) := by
  rw [centeredAddressDisplacement_first_difference_identity positive (ratio_upper.trans_lt upper_less_one), abs_neg]
  apply (abs_add_le _ _).trans
  simp only [abs_mul, Nat.abs_cast,
    abs_of_nonneg (pow_nonneg positive.le (verticalDepth+tailDepth-1)),
    abs_of_nonneg (pow_nonneg positive.le (verticalDepth+tailDepth))]
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (address_shared_prefix_bound positive.le (ratio_upper.trans_lt upper_less_one) first second depth agreement)
      (mul_nonneg (Nat.cast_nonneg (α := ℝ) (verticalDepth+tailDepth))
        (pow_nonneg positive.le (verticalDepth+tailDepth-1))))
    (mul_le_mul_of_nonneg_left
      (address_shared_prefix_derivative_bound positive ratio_upper upper_less_one first second depth agreement)
      (pow_nonneg positive.le _))

end LambdaCantor.AE
