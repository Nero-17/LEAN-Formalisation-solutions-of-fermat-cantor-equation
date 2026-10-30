import LambdaCantor.Last.NonlinearGeometry
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
namespace LambdaCantor.Last

/-- The ordinary one-variable mean value inequalities, including both endpoints. -/
theorem increment_bounds_of_hasDerivAt
    {function derivative : ℝ → ℝ} {lower upper : ℝ}
    (hderivative : ∀ point ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt function (derivative point) point)
    (hbounds : ∀ point ∈ Set.Icc (0 : ℝ) 1,
      lower ≤ derivative point ∧ derivative point ≤ upper)
    {first second : ℝ} (hfirst : first ∈ Set.Icc (0 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (0 : ℝ) 1) (horder : first ≤ second) :
    lower * (second - first) ≤ function second - function first ∧
      function second - function first ≤ upper * (second - first) := by
  have hcontinuous : ContinuousOn function (Set.Icc (0 : ℝ) 1) :=
    fun point hpoint => (hderivative point hpoint).continuousAt.continuousWithinAt
  have hdifferentiable : DifferentiableOn ℝ function (interior (Set.Icc (0 : ℝ) 1)) :=
    fun point hpoint =>
      (hderivative point (interior_subset hpoint)).differentiableAt.differentiableWithinAt
  constructor
  · apply (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
      hcontinuous hdifferentiable _ first hfirst second hsecond horder
    intro point hpoint
    rw [(hderivative point (interior_subset hpoint)).deriv]
    exact (hbounds point (interior_subset hpoint)).1
  · apply (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
      hcontinuous hdifferentiable _ first hfirst second hsecond horder
    intro point hpoint
    rw [(hderivative point (interior_subset hpoint)).deriv]
    exact (hbounds point (interior_subset hpoint)).2

/-- Partial derivatives with the paper's rectangular bounds imply the increment
interface used by the nonlinear corner geometry. -/
theorem coordinateGrowth_of_partial_derivatives
    {function : (ℝ × ℝ) → ℝ} {derivativeS derivativeT : ℝ → ℝ → ℝ}
    {lowerS upperS lowerT upperT : ℝ}
    (hderivativeS : ∀ width ∈ Set.Icc (0 : ℝ) 1,
      ∀ height ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun coordinate => function (coordinate, height))
        (derivativeS width height) width)
    (hderivativeT : ∀ width ∈ Set.Icc (0 : ℝ) 1,
      ∀ height ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun coordinate => function (width, coordinate))
        (derivativeT width height) height)
    (hboundS : ∀ width ∈ Set.Icc (0 : ℝ) 1,
      ∀ height ∈ Set.Icc (0 : ℝ) 1,
      lowerS ≤ derivativeS width height ∧ derivativeS width height ≤ upperS)
    (hboundT : ∀ width ∈ Set.Icc (0 : ℝ) 1,
      ∀ height ∈ Set.Icc (0 : ℝ) 1,
      lowerT ≤ derivativeT width height ∧ derivativeT width height ≤ upperT) :
    CoordinateGrowth function lowerS upperS lowerT upperT where
  horizontal first second height hfirst hsecond hheight horder :=
    increment_bounds_of_hasDerivAt
      (fun point hpoint => hderivativeS point hpoint height hheight)
      (fun point hpoint => hboundS point hpoint height hheight) hfirst hsecond horder
  vertical first second width hfirst hsecond hwidth horder :=
    increment_bounds_of_hasDerivAt
      (fun point hpoint => hderivativeT width hwidth point hpoint)
      (fun point hpoint => hboundT width hwidth point hpoint) hfirst hsecond horder

end LambdaCantor.Last
