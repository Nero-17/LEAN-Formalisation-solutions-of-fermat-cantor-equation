import LambdaCantor.AE.CenteredDisplacement
import LambdaCantor.AE.CenteredAddressSecond

noncomputable section
namespace LambdaCantor.AE

def centeredDisplacementFirst (verticalDepth tailDepth : ℕ) (digits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  (verticalDepth : ℝ) * ratio ^ (verticalDepth - 1) -
    ((verticalDepth + tailDepth : ℕ) : ℝ) * ratio ^ (verticalDepth + tailDepth - 1) * address ratio digits -
    ratio ^ (verticalDepth + tailDepth) * deriv (fun parameter => address parameter digits) ratio

def centeredDisplacementSecond (verticalDepth tailDepth : ℕ) (digits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  (verticalDepth : ℝ) * ((verticalDepth - 1 : ℕ) : ℝ) * ratio ^ (verticalDepth - 1 - 1) -
    ((verticalDepth + tailDepth : ℕ) : ℝ) * ((verticalDepth + tailDepth - 1 : ℕ) : ℝ) *
      ratio ^ (verticalDepth + tailDepth - 1 - 1) * address ratio digits -
    2 * ((verticalDepth + tailDepth : ℕ) : ℝ) * ratio ^ (verticalDepth + tailDepth - 1) *
      deriv (fun parameter => address parameter digits) ratio -
    ratio ^ (verticalDepth + tailDepth) * deriv (deriv (fun parameter => address parameter digits)) ratio

theorem centeredDisplacement_first_actual (verticalDepth tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1) :
    HasDerivAt (centeredAddressDisplacement verticalDepth tailDepth digits)
      (centeredDisplacementFirst verticalDepth tailDepth digits ratio) ratio := by
  have haddress := (hasDerivAt_address_parameter hpositive hless digits).differentiableAt.hasDerivAt
  have hmodel := (hasDerivAt_pow verticalDepth ratio).sub
    ((hasDerivAt_pow (verticalDepth + tailDepth) ratio).mul haddress)
  have hfunction := hmodel.congr_of_eventuallyEq
    (f₁ := centeredAddressDisplacement verticalDepth tailDepth digits)
    (Filter.Eventually.of_forall (fun parameter => by
      simp only [centeredAddressDisplacement, Pi.sub_apply, Pi.mul_apply, pow_add]
      ring))
  apply hfunction.congr_deriv
  unfold centeredDisplacementFirst
  ring

theorem centeredDisplacement_second_actual (verticalDepth tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1) :
    HasDerivAt (centeredDisplacementFirst verticalDepth tailDepth digits)
      (centeredDisplacementSecond verticalDepth tailDepth digits ratio) ratio := by
  have haddress := (hasDerivAt_address_parameter hpositive hless digits).differentiableAt.hasDerivAt
  have haddressSecond := (centered_address_second_hasDerivAt digits hpositive hless).differentiableAt.hasDerivAt
  have hfirst := (hasDerivAt_pow (verticalDepth - 1) ratio).const_mul (verticalDepth : ℝ)
  have hsecond := ((hasDerivAt_pow (verticalDepth + tailDepth - 1) ratio).const_mul
    ((verticalDepth + tailDepth : ℕ) : ℝ)).mul haddress
  have hthird := (hasDerivAt_pow (verticalDepth + tailDepth) ratio).mul haddressSecond
  have hmodel := (hfirst.sub hsecond).sub hthird
  have hfunction := hmodel.congr_of_eventuallyEq
    (f₁ := centeredDisplacementFirst verticalDepth tailDepth digits)
    (Filter.Eventually.of_forall (fun _ => rfl))
  apply hfunction.congr_deriv
  unfold centeredDisplacementSecond
  ring

theorem centeredDisplacement_second_bound (verticalDepth tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio firstBound secondBound : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1)
    (hfirst : |deriv (fun parameter => address parameter digits) ratio| ≤ firstBound)
    (hsecond : |deriv (deriv (fun parameter => address parameter digits)) ratio| ≤ secondBound) :
    |centeredDisplacementSecond verticalDepth tailDepth digits ratio| ≤
      (verticalDepth : ℝ) * ((verticalDepth - 1 : ℕ) : ℝ) * ratio ^ (verticalDepth - 1 - 1) +
      ((verticalDepth + tailDepth : ℕ) : ℝ) * ((verticalDepth + tailDepth - 1 : ℕ) : ℝ) *
        ratio ^ (verticalDepth + tailDepth - 1 - 1) +
      2 * ((verticalDepth + tailDepth : ℕ) : ℝ) * ratio ^ (verticalDepth + tailDepth - 1) * firstBound +
      ratio ^ (verticalDepth + tailDepth) * secondBound := by
  have haddress := cantorSet_subset_unitInterval hpositive.le hless
    (show address ratio digits ∈ cantorSet ratio from ⟨digits, rfl⟩)
  unfold centeredDisplacementSecond
  apply (abs_sub _ _).trans
  apply add_le_add
  · apply (abs_sub _ _).trans
    apply add_le_add
    · apply (abs_sub _ _).trans
      apply add_le_add
      · rw [abs_of_nonneg (by positivity)]
      · rw [abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg haddress.1]
        exact mul_le_of_le_one_right (by positivity) haddress.2
    · rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hfirst (by positivity)
  · rw [abs_mul, abs_of_nonneg (pow_nonneg hpositive.le _)]
    exact mul_le_mul_of_nonneg_left hsecond (pow_nonneg hpositive.le _)

end LambdaCantor.AE
