import LambdaCantor.AE.CenteredHorizontalMixed
import LambdaCantor.AE.CenteredLinearMixed
import LambdaCantor.AE.CenteredVerticalMixed

noncomputable section

namespace LambdaCantor.AE

def centeredHorizontalPrefixEnvelope (exponent : ℝ) (tailDepth depth : ℕ) (ratio upper : ℝ) : ℝ :=
  exponent *
    ((tailDepth : ℝ)*ratio^(tailDepth-1)*ratio^depth + ratio^tailDepth*
      ((depth : ℝ)*ratio^(depth-1) + 2*addressParameterDerivativeBound upper*ratio^depth)) +
  (exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) *
    (ratio^tailDepth*ratio^depth) *
    ((tailDepth : ℝ)*ratio^(tailDepth-1) + ratio^tailDepth*addressParameterDerivativeBound upper)

theorem centeredNormalizedResidual_derivative_decomposition
    (exponent : ℝ) (horizontalDepth verticalDepth tailDepth : ℕ) (digits : ℕ → Bool × Bool)
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1)
    (tail_small : ratio^tailDepth ≤ 1/2) (vertical_small : ratio^verticalDepth ≤ 1/2) :
    deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) ratio =
      deriv (fun parameter => (centeredHorizontalFactor tailDepth (fun index => (digits index).1) parameter)^exponent) ratio +
      deriv (centeredLinearVertical exponent horizontalDepth verticalDepth tailDepth (fun index => (digits index).2)) ratio +
      centeredRemainderFirst exponent horizontalDepth verticalDepth tailDepth (fun index => (digits index).2) ratio := by
  have address_nonnegative := address_nonnegative positive.le less_one (fun index => (digits index).1)
  have horizontal_positive : 0 < centeredHorizontalFactor tailDepth (fun index => (digits index).1) ratio := by
    unfold centeredHorizontalFactor
    nlinarith [mul_nonneg (pow_nonneg positive.le tailDepth) address_nonnegative]
  have horizontal := (centeredHorizontalFactor_hasDerivAt tailDepth (fun index => (digits index).1) positive less_one).rpow_const
    (p := exponent) (Or.inl horizontal_positive.ne')
  have linear := centeredLinearVertical_differentiableAt exponent horizontalDepth verticalDepth tailDepth
    (fun index => (digits index).2) positive less_one
  have remainder := centeredRemainderFunction_hasDerivAt exponent horizontalDepth verticalDepth tailDepth
    (fun index => (digits index).2) positive less_one (by linarith)
  have identity : centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits =
      (fun parameter => (centeredHorizontalFactor tailDepth (fun index => (digits index).1) parameter)^exponent +
        centeredLinearVertical exponent horizontalDepth verticalDepth tailDepth (fun index => (digits index).2) parameter +
        centeredRemainderFunction exponent horizontalDepth verticalDepth tailDepth (fun index => (digits index).2) parameter) := by
    funext parameter
    unfold centeredNormalizedResidual centeredLinearVertical
    ring
  rw [identity]
  have derivative := ((horizontal.differentiableAt.hasDerivAt.add linear.hasDerivAt).add remainder).congr_of_eventuallyEq
    (f₁ := fun parameter =>
      (centeredHorizontalFactor tailDepth (fun index => (digits index).1) parameter)^exponent +
        centeredLinearVertical exponent horizontalDepth verticalDepth tailDepth (fun index => (digits index).2) parameter +
        centeredRemainderFunction exponent horizontalDepth verticalDepth tailDepth (fun index => (digits index).2) parameter)
    (Filter.Eventually.of_forall (fun _ => rfl))
  exact derivative.deriv

/-- Full actual same-prefix parameter derivative difference, with the main
resonant coefficient and the exponentially small vertical remainder treated
separately before their final scale estimates. -/
theorem centeredNormalizedResidual_first_shared_prefix_bound
    {exponent ratio upper : ℝ} (exponent_greater_one : 1 < exponent)
    (positive : 0 < ratio) (ratio_upper : ratio ≤ upper) (upper_less_one : upper < 1)
    (horizontalDepth verticalDepth tailDepth depth : ℕ)
    (tail_small : ratio^tailDepth ≤ 1/2) (vertical_small : ratio^verticalDepth ≤ 1/2)
    (first second : ℕ → Bool × Bool) (agreement : ∀ index < depth, first index = second index) :
    |deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth first) ratio -
      deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth second) ratio| ≤
      centeredHorizontalPrefixEnvelope exponent tailDepth depth ratio upper +
        centeredLinearPrefixEnvelope exponent horizontalDepth verticalDepth tailDepth depth ratio upper +
        centeredRemainderPrefixEnvelope exponent horizontalDepth verticalDepth tailDepth depth ratio upper := by
  have first_agreement : ∀ index < depth, (first index).1 = (second index).1 :=
    fun index before => congrArg Prod.fst (agreement index before)
  have second_agreement : ∀ index < depth, (first index).2 = (second index).2 :=
    fun index before => congrArg Prod.snd (agreement index before)
  have horizontal := centered_horizontal_shared_prefix_derivative_bound exponent_greater_one
    positive ratio_upper upper_less_one tailDepth depth tail_small
    (fun index => (first index).1) (fun index => (second index).1) first_agreement
  change _ ≤ centeredHorizontalPrefixEnvelope exponent tailDepth depth ratio upper at horizontal
  have linear := centeredLinearVertical_first_shared_prefix_bound (by linarith : 0 ≤ exponent)
    positive ratio_upper upper_less_one horizontalDepth verticalDepth tailDepth depth
    (fun index => (first index).2) (fun index => (second index).2) second_agreement
  have remainder := centeredRemainderFirst_shared_prefix_bound exponent_greater_one
    positive ratio_upper upper_less_one horizontalDepth verticalDepth tailDepth depth vertical_small
    (fun index => (first index).2) (fun index => (second index).2) second_agreement
  rw [centeredNormalizedResidual_derivative_decomposition exponent horizontalDepth verticalDepth tailDepth first
    positive (ratio_upper.trans_lt upper_less_one) tail_small vertical_small,
    centeredNormalizedResidual_derivative_decomposition exponent horizontalDepth verticalDepth tailDepth second
      positive (ratio_upper.trans_lt upper_less_one) tail_small vertical_small]
  have decomposition :
      (deriv (fun parameter => (centeredHorizontalFactor tailDepth (fun index => (first index).1) parameter)^exponent) ratio +
        deriv (centeredLinearVertical exponent horizontalDepth verticalDepth tailDepth (fun index => (first index).2)) ratio +
        centeredRemainderFirst exponent horizontalDepth verticalDepth tailDepth (fun index => (first index).2) ratio) -
      (deriv (fun parameter => (centeredHorizontalFactor tailDepth (fun index => (second index).1) parameter)^exponent) ratio +
        deriv (centeredLinearVertical exponent horizontalDepth verticalDepth tailDepth (fun index => (second index).2)) ratio +
        centeredRemainderFirst exponent horizontalDepth verticalDepth tailDepth (fun index => (second index).2) ratio) =
      ((deriv (fun parameter => (centeredHorizontalFactor tailDepth (fun index => (first index).1) parameter)^exponent) ratio -
        deriv (fun parameter => (centeredHorizontalFactor tailDepth (fun index => (second index).1) parameter)^exponent) ratio) +
       (deriv (centeredLinearVertical exponent horizontalDepth verticalDepth tailDepth (fun index => (first index).2)) ratio -
        deriv (centeredLinearVertical exponent horizontalDepth verticalDepth tailDepth (fun index => (second index).2)) ratio)) +
      (centeredRemainderFirst exponent horizontalDepth verticalDepth tailDepth (fun index => (first index).2) ratio -
        centeredRemainderFirst exponent horizontalDepth verticalDepth tailDepth (fun index => (second index).2) ratio) := by ring
  rw [decomposition]
  apply (abs_add_le _ _).trans
  have first_two := (abs_add_le _ _).trans (add_le_add horizontal linear)
  exact add_le_add first_two remainder

end LambdaCantor.AE
