import LambdaCantor.AE.CenteredResidual
import LambdaCantor.First.PrefixEstimates

noncomputable section

namespace LambdaCantor.AE

def centeredLinearVertical (exponent : ℝ) (horizontalDepth verticalDepth tailDepth : ℕ)
    (digits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  -exponent * ratio^((verticalDepth : ℝ)-exponent*horizontalDepth) * centeredTailFactor tailDepth digits ratio

theorem centeredLinearVertical_differentiableAt (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1) :
    DifferentiableAt ℝ (centeredLinearVertical exponent horizontalDepth verticalDepth tailDepth digits) ratio := by
  have coefficient := ((hasDerivAt_id ratio).rpow_const
    (p := (verticalDepth : ℝ)-exponent*horizontalDepth) (Or.inl positive.ne')).const_mul (-exponent)
  exact (coefficient.mul (centeredTailFactor_hasDerivAt tailDepth digits positive less_one)).differentiableAt

/-- The large vertical cylinder depth cancels from the main derivative
coefficient before taking absolute values. Only m minus alpha k plus L remains. -/
theorem centeredLinearVertical_first_difference_identity (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth : ℕ) (first second : ℕ → Bool)
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1) :
    deriv (centeredLinearVertical exponent horizontalDepth verticalDepth tailDepth first) ratio -
      deriv (centeredLinearVertical exponent horizontalDepth verticalDepth tailDepth second) ratio =
      exponent * ((verticalDepth : ℝ)-exponent*horizontalDepth+tailDepth) *
        ratio^((verticalDepth : ℝ)-exponent*horizontalDepth+tailDepth-1) *
          (address ratio first-address ratio second) +
      exponent * ratio^((verticalDepth : ℝ)-exponent*horizontalDepth+tailDepth) *
        (addressParameterDerivative ratio first-addressParameterDerivative ratio second) := by
  have actual :=
    ((centeredLinearVertical_differentiableAt exponent horizontalDepth verticalDepth tailDepth first positive less_one).hasDerivAt).sub
      ((centeredLinearVertical_differentiableAt exponent horizontalDepth verticalDepth tailDepth second positive less_one).hasDerivAt)
  have coefficient := ((hasDerivAt_id ratio).rpow_const
    (p := (verticalDepth : ℝ)-exponent*horizontalDepth+tailDepth) (Or.inl positive.ne')).const_mul exponent
  have factored := coefficient.mul ((hasDerivAt_address_parameter positive less_one first).sub
    (hasDerivAt_address_parameter positive less_one second))
  have same_function :
      (fun parameter => centeredLinearVertical exponent horizontalDepth verticalDepth tailDepth first parameter -
        centeredLinearVertical exponent horizontalDepth verticalDepth tailDepth second parameter) =ᶠ[nhds ratio]
      (fun parameter => (exponent*parameter^((verticalDepth : ℝ)-exponent*horizontalDepth+tailDepth)) *
        (address parameter first-address parameter second)) := by
    filter_upwards [lt_mem_nhds positive] with parameter parameter_positive
    unfold centeredLinearVertical centeredTailFactor
    rw [Real.rpow_add parameter_positive, Real.rpow_natCast]
    ring
  have equality := actual.unique (factored.congr_of_eventuallyEq same_function)
  simpa only [one_mul, mul_assoc, id_eq, Pi.sub_apply] using equality

def centeredLinearPrefixEnvelope (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (ratio upper : ℝ) : ℝ :=
  |exponent * ((verticalDepth : ℝ)-exponent*horizontalDepth+tailDepth)| *
    ratio^((verticalDepth : ℝ)-exponent*horizontalDepth+tailDepth-1)*ratio^depth +
  exponent * ratio^((verticalDepth : ℝ)-exponent*horizontalDepth+tailDepth) *
    ((depth : ℝ)*ratio^(depth-1) + 2*addressParameterDerivativeBound upper*ratio^depth)

theorem centeredLinearVertical_first_shared_prefix_bound
    {exponent ratio upper : ℝ} (exponent_nonnegative : 0 ≤ exponent)
    (positive : 0 < ratio) (ratio_upper : ratio ≤ upper) (upper_less_one : upper < 1)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (first second : ℕ → Bool)
    (agreement : ∀ index < depth, first index = second index) :
    |deriv (centeredLinearVertical exponent horizontalDepth verticalDepth tailDepth first) ratio -
      deriv (centeredLinearVertical exponent horizontalDepth verticalDepth tailDepth second) ratio| ≤
      centeredLinearPrefixEnvelope exponent horizontalDepth verticalDepth tailDepth depth ratio upper := by
  rw [centeredLinearVertical_first_difference_identity exponent horizontalDepth verticalDepth tailDepth first second
    positive (ratio_upper.trans_lt upper_less_one)]
  unfold centeredLinearPrefixEnvelope
  apply (abs_add_le _ _).trans
  simp only [abs_mul, abs_of_nonneg exponent_nonnegative,
    abs_of_nonneg (Real.rpow_nonneg positive.le _)]
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (address_shared_prefix_bound positive.le (ratio_upper.trans_lt upper_less_one) first second depth agreement)
      (by positivity))
    (mul_le_mul_of_nonneg_left
      (address_shared_prefix_derivative_bound positive ratio_upper upper_less_one first second depth agreement)
      (by positivity))

end LambdaCantor.AE
