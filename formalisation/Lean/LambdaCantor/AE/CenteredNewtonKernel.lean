import LambdaCantor.AE.CenteredTaylor
import LambdaCantor.AE.AffineConvolutionMeasure

noncomputable section
open MeasureTheory

namespace LambdaCantor.AE

/-- The exact normalized residual with two real tail coordinates. -/
def centeredTailResidual (exponent : ℝ) (horizontalDepth verticalDepth tailDepth : ℕ)
    (ratio first second : ℝ) : ℝ :=
  (1 - ratio ^ tailDepth + ratio ^ tailDepth * first) ^ exponent +
    ((1 - ratio ^ verticalDepth + ratio ^ (verticalDepth + tailDepth) * second) ^ exponent - 1) /
      ratio ^ (exponent * horizontalDepth)

theorem centeredTailResidual_actual (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth : ℕ) {ratio : ℝ}
    (ratio_positive : 0 < ratio) (ratio_less_one : ratio < 1)
    (first second : ℝ) (first_nonnegative : 0 ≤ first) :
    centeredTailResidual exponent horizontalDepth verticalDepth tailDepth ratio first second =
      (((centeredCylinder ratio horizontalDepth verticalDepth tailDepth (first, second)).1 ^ exponent +
        (centeredCylinder ratio horizontalDepth verticalDepth tailDepth (first, second)).2 ^ exponent - 1) /
          ratio ^ (exponent * horizontalDepth)) := by
  have horizontal_nonnegative : 0 ≤ 1 - ratio ^ tailDepth + ratio ^ tailDepth * first := by
    have power_bound := pow_le_one₀ ratio_positive.le ratio_less_one.le (n := tailDepth)
    nlinarith [mul_nonneg (pow_nonneg ratio_positive.le tailDepth) first_nonnegative]
  have horizontal_factor :
      (ratio ^ horizontalDepth * (1 - ratio ^ tailDepth + ratio ^ tailDepth * first)) ^ exponent =
        ratio ^ (exponent * horizontalDepth) *
          (1 - ratio ^ tailDepth + ratio ^ tailDepth * first) ^ exponent := by
    rw [Real.mul_rpow (pow_nonneg ratio_positive.le _) horizontal_nonnegative,
      ← Real.rpow_natCast_mul ratio_positive.le]
    congr 2
    ring
  unfold centeredTailResidual centeredCylinder
  simp only [Prod.fst, Prod.snd]
  rw [horizontal_factor]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos ratio_positive (exponent * horizontalDepth))]
  <;> ring

/-- The complete Newton observable. Its constant includes the residual at the
freezing point, which is allowed to be away from the root. -/
def centeredNewtonValue (freezing residual parameterDerivative firstDerivative secondDerivative : ℝ)
    (first second : ℝ) : ℝ :=
  freezing - (residual + firstDerivative * first + secondDerivative * second) / parameterDerivative

def centeredNewtonLaw (ratio freezing residual parameterDerivative firstDerivative secondDerivative : ℝ) :
    Measure ℝ :=
  affineConvolutionProbability ratio (freezing - residual / parameterDerivative)
    (-firstDerivative / parameterDerivative) (-secondDerivative / parameterDerivative)

instance (ratio freezing residual parameterDerivative firstDerivative secondDerivative : ℝ) :
    IsProbabilityMeasure
      (centeredNewtonLaw ratio freezing residual parameterDerivative firstDerivative secondDerivative) := by
  unfold centeredNewtonLaw
  infer_instance

/-- The law in the paper is the law of the complete displayed Newton expression. -/
theorem centeredNewtonLaw_eq_address_map
    (ratio freezing residual parameterDerivative firstDerivative secondDerivative : ℝ) :
    centeredNewtonLaw ratio freezing residual parameterDerivative firstDerivative secondDerivative =
      (addressProbability.prod addressProbability).map
        (fun digits : (ℕ → Bool) × (ℕ → Bool) =>
          centeredNewtonValue freezing residual parameterDerivative firstDerivative secondDerivative
            (address ratio digits.1) (address ratio digits.2)) := by
  rw [centeredNewtonLaw, affineConvolutionProbability_eq_address_map]
  congr 1
  funext digits
  unfold centeredNewtonValue
  ring

/-- Dividing the actual Taylor remainder by the transverse parameter slope
gives the root/Newton displacement, including the constant residual term. -/
theorem centeredNewton_error_of_residual_remainder
    {root freezing residual parameterDerivative firstDerivative secondDerivative first second error : ℝ}
    (derivative_nonzero : parameterDerivative ≠ 0)
    (remainder : |residual + parameterDerivative * (root - freezing) +
      firstDerivative * first + secondDerivative * second| ≤ error) :
    |root - centeredNewtonValue freezing residual parameterDerivative firstDerivative secondDerivative
      first second| ≤ error / |parameterDerivative| := by
  have identity : root -
      centeredNewtonValue freezing residual parameterDerivative firstDerivative secondDerivative first second =
      (residual + parameterDerivative * (root - freezing) +
        firstDerivative * first + secondDerivative * second) / parameterDerivative := by
    unfold centeredNewtonValue
    field_simp [derivative_nonzero]
    <;> ring
  rw [identity, abs_div]
  exact div_le_div_of_nonneg_right remainder (abs_nonneg _)

end LambdaCantor.AE
