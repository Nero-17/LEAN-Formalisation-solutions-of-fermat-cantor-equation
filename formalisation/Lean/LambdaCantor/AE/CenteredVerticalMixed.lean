import LambdaCantor.AE.CenteredTaylorDifference
import LambdaCantor.AE.CenteredDisplacementPrefix
import LambdaCantor.AE.CenteredRemainderDerivatives
import Mathlib.Tactic.GCongr

noncomputable section

namespace LambdaCantor.AE

def centeredRemainderPrefixEnvelope (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (ratio upper : ℝ) : ℝ :=
  |(-exponent*(horizontalDepth : ℝ))| * ratio^(-exponent*horizontalDepth-1) *
    ((exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) * ratio^verticalDepth *
      (ratio^(verticalDepth+tailDepth)*ratio^depth)) +
  ratio^(-exponent*(horizontalDepth : ℝ)) *
    (((exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) * ratio^verticalDepth) *
      (((verticalDepth+tailDepth : ℕ) : ℝ)*ratio^(verticalDepth+tailDepth-1)*ratio^depth +
        ratio^(verticalDepth+tailDepth)*
          ((depth : ℝ)*ratio^(depth-1) + 2*addressParameterDerivativeBound upper*ratio^depth)) +
      ((exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) *
        (ratio^(verticalDepth+tailDepth)*ratio^depth)) *
          ((verticalDepth : ℝ)*ratio^(verticalDepth-1) + ratio^verticalDepth*
            ((tailDepth : ℝ)*ratio^(tailDepth-1) + ratio^tailDepth*addressParameterDerivativeBound upper)))

/-- Actual normalized vertical-remainder derivative difference. The envelope
retains lambda to power twice m minus alpha k and every shared-prefix factor,
so phase control and m-squared exponential decay can be used afterward. -/
theorem centeredRemainderFirst_shared_prefix_bound
    {exponent ratio upper : ℝ} (exponent_greater_one : 1 < exponent)
    (positive : 0 < ratio) (ratio_upper : ratio ≤ upper) (upper_less_one : upper < 1)
    (horizontalDepth verticalDepth tailDepth depth : ℕ)
    (vertical_small : ratio^verticalDepth ≤ 1/2)
    (first second : ℕ → Bool) (agreement : ∀ index < depth, first index = second index) :
    |centeredRemainderFirst exponent horizontalDepth verticalDepth tailDepth first ratio -
      centeredRemainderFirst exponent horizontalDepth verticalDepth tailDepth second ratio| ≤
      centeredRemainderPrefixEnvelope exponent horizontalDepth verticalDepth tailDepth depth ratio upper := by
  have less_one := ratio_upper.trans_lt upper_less_one
  have exponent_positive : 0 < exponent := by linarith
  have exponent_minus_positive : 0 < exponent-1 := sub_pos.mpr exponent_greater_one
  have address_bound_nonnegative : 0 ≤ addressParameterDerivativeBound upper :=
    (abs_nonneg _).trans (address_parameter_derivative_bound positive.le ratio_upper upper_less_one first)
  have first_bounds := centeredAddressDisplacement_bounds verticalDepth tailDepth first positive less_one
  have second_bounds := centeredAddressDisplacement_bounds verticalDepth tailDepth second positive less_one
  have maximum_bound :
      max (centeredAddressDisplacement verticalDepth tailDepth first ratio)
        (centeredAddressDisplacement verticalDepth tailDepth second ratio) ≤ ratio^verticalDepth :=
    max_le first_bounds.2 second_bounds.2
  have displacement_difference := centeredAddressDisplacement_shared_prefix_bound positive less_one
    verticalDepth tailDepth depth first second agreement
  have velocity_difference := centeredAddressDisplacement_first_shared_prefix_bound positive ratio_upper upper_less_one
    verticalDepth tailDepth depth first second agreement
  rw [(centeredDisplacement_first_actual verticalDepth tailDepth first positive less_one).deriv,
    (centeredDisplacement_first_actual verticalDepth tailDepth second positive less_one).deriv] at velocity_difference
  have second_velocity := centeredAddressDisplacement_derivative_bound verticalDepth tailDepth second
    positive ratio_upper upper_less_one
  rw [(centeredDisplacement_first_actual verticalDepth tailDepth second positive less_one).deriv] at second_velocity
  have difference := centered_normalized_first_difference_bound exponent_greater_one positive
    (show centeredAddressDisplacement verticalDepth tailDepth first ratio ∈ Set.Icc (0 : ℝ) (1/2) from
      ⟨first_bounds.1, first_bounds.2.trans vertical_small⟩)
    (show centeredAddressDisplacement verticalDepth tailDepth second ratio ∈ Set.Icc (0 : ℝ) (1/2) from
      ⟨second_bounds.1, second_bounds.2.trans vertical_small⟩)
    (scaleExponent := -exponent*(horizontalDepth : ℝ))
    (firstVelocity := centeredDisplacementFirst verticalDepth tailDepth first ratio)
    (secondVelocity := centeredDisplacementFirst verticalDepth tailDepth second ratio)
  have actual_difference :
      |centeredRemainderFirst exponent horizontalDepth verticalDepth tailDepth first ratio -
        centeredRemainderFirst exponent horizontalDepth verticalDepth tailDepth second ratio| ≤
      |(-exponent*(horizontalDepth : ℝ))| * ratio^(-exponent*horizontalDepth-1) *
        ((exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) *
          max (centeredAddressDisplacement verticalDepth tailDepth first ratio)
            (centeredAddressDisplacement verticalDepth tailDepth second ratio) *
          |centeredAddressDisplacement verticalDepth tailDepth first ratio -
            centeredAddressDisplacement verticalDepth tailDepth second ratio|) +
      ratio^(-exponent*(horizontalDepth : ℝ)) *
        (((exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) *
            centeredAddressDisplacement verticalDepth tailDepth first ratio) *
          |centeredDisplacementFirst verticalDepth tailDepth first ratio -
            centeredDisplacementFirst verticalDepth tailDepth second ratio| +
        ((exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) *
          |centeredAddressDisplacement verticalDepth tailDepth first ratio -
            centeredAddressDisplacement verticalDepth tailDepth second ratio|) *
          |centeredDisplacementFirst verticalDepth tailDepth second ratio|) := by
    simpa only [centeredRemainderFirst, mul_assoc] using difference
  apply actual_difference.trans
  unfold centeredRemainderPrefixEnvelope
  gcongr <;> first | exact maximum_bound | exact first_bounds.2 |
    exact displacement_difference | exact velocity_difference | exact second_velocity | positivity

end LambdaCantor.AE
