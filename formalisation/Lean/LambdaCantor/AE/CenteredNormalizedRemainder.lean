import LambdaCantor.AE.CenteredTaylorComposition

noncomputable section
namespace LambdaCantor.AE

/-- Product rule for the exact normalized remainder. Take scaleExponent=-n*k
for the paper's division by λ^(n*k). -/
theorem centeredNormalizedRemainder_hasDerivAt
    {displacement : ℝ → ℝ} {parameter velocity exponent scaleExponent : ℝ}
    (hpositive : 0 < parameter) (hsmall : displacement parameter < 1)
    (hdisplacement : HasDerivAt displacement velocity parameter) :
    HasDerivAt (fun value => value ^ scaleExponent * centeredTaylorRemainder exponent (displacement value))
      (scaleExponent * parameter ^ (scaleExponent - 1) *
          centeredTaylorRemainder exponent (displacement parameter) +
        parameter ^ scaleExponent * centeredTaylorFirst exponent (displacement parameter) * velocity)
      parameter := by
  have hpower := (hasDerivAt_id parameter).rpow_const
    (p := scaleExponent) (Or.inl (ne_of_gt hpositive))
  have hproduct := hpower.mul
    (centeredTaylor_comp_hasDerivAt hdisplacement hsmall (exponent := exponent))
  have hfunction := hproduct.congr_of_eventuallyEq
    (f₁ := fun value : ℝ =>
      value ^ scaleExponent * centeredTaylorRemainder exponent (displacement value))
    (Filter.Eventually.of_forall (fun _ => rfl))
  apply hfunction.congr_deriv
  simp only [one_mul, id_eq]
  ring

theorem centeredNormalizedRemainder_second
    {displacement velocity : ℝ → ℝ} {parameter acceleration exponent scaleExponent : ℝ}
    (hpositive : 0 < parameter) (hsmall : displacement parameter < 1)
    (hdisplacement : HasDerivAt displacement (velocity parameter) parameter)
    (hvelocity : HasDerivAt velocity acceleration parameter) :
    HasDerivAt (fun value =>
      scaleExponent * value ^ (scaleExponent - 1) * centeredTaylorRemainder exponent (displacement value) +
        value ^ scaleExponent * (centeredTaylorFirst exponent (displacement value) * velocity value))
      (scaleExponent * (scaleExponent - 1) * parameter ^ (scaleExponent - 2) *
          centeredTaylorRemainder exponent (displacement parameter) +
        2 * scaleExponent * parameter ^ (scaleExponent - 1) *
          centeredTaylorFirst exponent (displacement parameter) * velocity parameter +
        parameter ^ scaleExponent *
          (centeredTaylorSecond exponent (displacement parameter) * (velocity parameter) ^ 2 +
            centeredTaylorFirst exponent (displacement parameter) * acceleration)) parameter := by
  have hpower := (hasDerivAt_id parameter).rpow_const
    (p := scaleExponent) (Or.inl (ne_of_gt hpositive))
  have hpowerFirst := ((hasDerivAt_id parameter).rpow_const
    (p := scaleExponent - 1) (Or.inl (ne_of_gt hpositive))).const_mul scaleExponent
  have hremainder := centeredTaylor_comp_hasDerivAt hdisplacement hsmall (exponent := exponent)
  have hremainderFirst := centeredTaylor_comp_second hdisplacement hvelocity hsmall (exponent := exponent)
  have hshift : scaleExponent - 1 - 1 = scaleExponent - 2 := by ring
  have hproduct := (hpowerFirst.mul hremainder).add (hpower.mul hremainderFirst)
  have hfunction := hproduct.congr_of_eventuallyEq
    (f₁ := fun value : ℝ =>
      scaleExponent * value ^ (scaleExponent - 1) * centeredTaylorRemainder exponent (displacement value) +
        value ^ scaleExponent * (centeredTaylorFirst exponent (displacement value) * velocity value))
    (Filter.Eventually.of_forall (fun _ => rfl))
  apply hfunction.congr_deriv
  simp only [one_mul, id_eq, hshift]
  ring

end LambdaCantor.AE
