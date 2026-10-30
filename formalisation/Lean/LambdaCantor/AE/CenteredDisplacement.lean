import LambdaCantor.AE.CenteredTaylorComposition
import LambdaCantor.First.AddressParameter

noncomputable section
namespace LambdaCantor.AE

def centeredAddressDisplacement (verticalDepth tailDepth : ℕ) (digits : ℕ → Bool)
    (ratio : ℝ) : ℝ := ratio ^ verticalDepth * (1 - ratio ^ tailDepth * address ratio digits)

theorem centeredAddressDisplacement_hasDerivAt
    (verticalDepth tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1) :
    HasDerivAt (centeredAddressDisplacement verticalDepth tailDepth digits)
      ((verticalDepth : ℝ) * ratio ^ (verticalDepth - 1) *
          (1 - ratio ^ tailDepth * address ratio digits) -
        ratio ^ verticalDepth * ((tailDepth : ℝ) * ratio ^ (tailDepth - 1) * address ratio digits +
          ratio ^ tailDepth * addressParameterDerivative ratio digits)) ratio := by
  have htail := (hasDerivAt_pow tailDepth ratio).mul (hasDerivAt_address_parameter hpositive hless digits)
  have hproduct := (hasDerivAt_pow verticalDepth ratio).mul (htail.const_sub 1)
  have hfunction := hproduct.congr_of_eventuallyEq
    (f₁ := centeredAddressDisplacement verticalDepth tailDepth digits)
    (Filter.Eventually.of_forall (fun _ => rfl))
  apply hfunction.congr_deriv
  simp only [Pi.mul_apply]
  ring

theorem centeredAddressDisplacement_bounds
    (verticalDepth tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1) :
    0 ≤ centeredAddressDisplacement verticalDepth tailDepth digits ratio ∧
      centeredAddressDisplacement verticalDepth tailDepth digits ratio ≤ ratio ^ verticalDepth := by
  have haddress := cantorSet_subset_unitInterval hpositive.le hless
    (show address ratio digits ∈ cantorSet ratio from ⟨digits, rfl⟩)
  have hbounds := centered_displacement_bounds hpositive hless verticalDepth tailDepth haddress
  have hpower : ratio ^ tailDepth ≤ 1 := pow_le_one₀ hpositive.le hless.le
  exact ⟨(mul_nonneg (pow_nonneg hpositive.le _) (sub_nonneg.mpr hpower)).trans hbounds.1,
    hbounds.2⟩

theorem centeredAddressDisplacement_derivative_bound
    (verticalDepth tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio upper : ℝ} (hpositive : 0 < ratio) (hupper : ratio ≤ upper) (hless : upper < 1) :
    |deriv (centeredAddressDisplacement verticalDepth tailDepth digits) ratio| ≤
      (verticalDepth : ℝ) * ratio ^ (verticalDepth - 1) + ratio ^ verticalDepth *
        ((tailDepth : ℝ) * ratio ^ (tailDepth - 1) +
          ratio ^ tailDepth * addressParameterDerivativeBound upper) := by
  have hratioLess := hupper.trans_lt hless
  have haddress := cantorSet_subset_unitInterval hpositive.le hratioLess
    (show address ratio digits ∈ cantorSet ratio from ⟨digits, rfl⟩)
  have htailPower : ratio ^ tailDepth ≤ 1 := pow_le_one₀ hpositive.le hratioLess.le
  have htail : 0 ≤ 1 - ratio ^ tailDepth * address ratio digits := by
    nlinarith [mul_le_mul_of_nonneg_left haddress.2 (pow_nonneg hpositive.le tailDepth)]
  have htailUpper : 1 - ratio ^ tailDepth * address ratio digits ≤ 1 := by
    nlinarith [mul_nonneg (pow_nonneg hpositive.le tailDepth) haddress.1]
  rw [(centeredAddressDisplacement_hasDerivAt verticalDepth tailDepth digits hpositive hratioLess).deriv]
  apply (abs_sub _ _).trans
  simp only [abs_mul, Nat.abs_cast, abs_of_nonneg (pow_nonneg hpositive.le (verticalDepth - 1)),
    abs_of_nonneg htail, abs_of_nonneg (pow_nonneg hpositive.le verticalDepth)]
  apply add_le_add
  · exact mul_le_of_le_one_right (by positivity) htailUpper
  · apply mul_le_mul_of_nonneg_left _ (pow_nonneg hpositive.le verticalDepth)
    apply (abs_add_le _ _).trans
    simp only [abs_mul, Nat.abs_cast, abs_of_nonneg (pow_nonneg hpositive.le (tailDepth - 1)),
      abs_of_nonneg haddress.1, abs_of_nonneg (pow_nonneg hpositive.le tailDepth)]
    exact add_le_add (mul_le_of_le_one_right (by positivity) haddress.2)
      (mul_le_mul_of_nonneg_left (address_parameter_derivative_bound hpositive.le hupper hless digits)
        (pow_nonneg hpositive.le tailDepth))

end LambdaCantor.AE
