import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith

noncomputable section
namespace LambdaCantor

/-- Quantitative transverse-root estimate used in the denominator bound.
The derivative and endpoint residual estimates remain explicit inputs. -/
theorem root_displacement_le {residual : ℝ → ℝ}
    {left right root slope error : ℝ}
    (hinterval : left ≤ right) (hroot : root ∈ Set.Icc left right)
    (hcontinuous : ContinuousOn residual (Set.Icc left right))
    (hdifferentiable : DifferentiableOn ℝ residual (Set.Ioo left right))
    (hslope : 0 < slope)
    (hderivative : ∀ parameter ∈ Set.Ioo left right,
      deriv residual parameter ≤ -slope)
    (hzero : residual root = 0) (herror : residual left ≤ error) :
    root - left ≤ error / slope := by
  have hchange := (convex_Icc left right).image_sub_le_mul_sub_of_deriv_le
    hcontinuous (by simpa only [interior_Icc] using hdifferentiable)
    (by simpa only [interior_Icc] using hderivative)
    left ⟨le_rfl, hinterval⟩ root hroot hroot.1
  rw [hzero] at hchange
  apply (le_div_iff₀ hslope).2
  nlinarith

/-- Negative derivative on an interval supplies the injectivity needed to
choose the unique root for each pair of Cantor addresses. -/
theorem strictAntiOn_of_uniform_negative_derivative {residual : ℝ → ℝ}
    {left right slope : ℝ}
    (hcontinuous : ContinuousOn residual (Set.Icc left right))
    (hslope : 0 < slope)
    (hderivative : ∀ parameter ∈ Set.Ioo left right,
      deriv residual parameter ≤ -slope) :
    StrictAntiOn residual (Set.Icc left right) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc left right) hcontinuous
  intro parameter hparameter
  have hbound := hderivative parameter (by simpa only [interior_Icc] using hparameter)
  linarith

end LambdaCantor
