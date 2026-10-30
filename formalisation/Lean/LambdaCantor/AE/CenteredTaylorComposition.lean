import LambdaCantor.AE.CenteredTaylor
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
namespace LambdaCantor.AE

/-- Exact chain rule for the centered remainder along a parameter-dependent
displacement. The address derivative enters through the displacement derivative. -/
theorem centeredTaylor_comp_hasDerivAt {displacement : ℝ → ℝ}
    {parameter velocity exponent : ℝ}
    (hdisplacement : HasDerivAt displacement velocity parameter)
    (hsmall : displacement parameter < 1) :
    HasDerivAt (fun value => centeredTaylorRemainder exponent (displacement value))
      (centeredTaylorFirst exponent (displacement parameter) * velocity) parameter :=
  (centeredTaylor_hasDerivAt exponent (displacement parameter) hsmall).comp parameter hdisplacement

theorem centeredTaylor_comp_second {displacement velocity : ℝ → ℝ}
    {parameter acceleration exponent : ℝ}
    (hdisplacement : HasDerivAt displacement (velocity parameter) parameter)
    (hvelocity : HasDerivAt velocity acceleration parameter)
    (hsmall : displacement parameter < 1) :
    HasDerivAt (fun value => centeredTaylorFirst exponent (displacement value) * velocity value)
      (centeredTaylorSecond exponent (displacement parameter) * (velocity parameter) ^ 2 +
        centeredTaylorFirst exponent (displacement parameter) * acceleration) parameter := by
  have hproduct := ((centeredTaylorFirst_hasDerivAt exponent (displacement parameter) hsmall).comp
    parameter hdisplacement).mul hvelocity
  have hfunction := hproduct.congr_of_eventuallyEq
    (f₁ := fun value => centeredTaylorFirst exponent (displacement value) * velocity value)
    (Filter.Eventually.of_forall (fun _ => rfl))
  apply hfunction.congr_deriv
  simp only [Function.comp_apply]
  ring

theorem centeredTaylor_comp_second_bound {exponent displacement velocity acceleration : ℝ}
    (hexponent : 1 < exponent) (hsmall : displacement ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    |centeredTaylorSecond exponent displacement * velocity ^ 2 +
      centeredTaylorFirst exponent displacement * acceleration| ≤
    (exponent * (exponent - 1) * max 1 ((1 / 2 : ℝ) ^ (exponent - 2))) *
      (velocity ^ 2 + displacement * |acceleration|) := by
  have hsecond := mul_le_mul_of_nonneg_right (centeredTaylorSecond_bound hexponent hsmall)
    (sq_nonneg velocity)
  have hfirst := mul_le_mul_of_nonneg_right (centeredTaylorFirst_bound hexponent hsmall)
    (abs_nonneg acceleration)
  calc
    _ ≤ |centeredTaylorSecond exponent displacement * velocity ^ 2| +
        |centeredTaylorFirst exponent displacement * acceleration| := abs_add_le _ _
    _ = |centeredTaylorSecond exponent displacement| * velocity ^ 2 +
        |centeredTaylorFirst exponent displacement| * |acceleration| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg velocity)]
    _ ≤ _ := by nlinarith

end LambdaCantor.AE
