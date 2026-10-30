import LambdaCantor.AE.CenteredNewtonKernel

noncomputable section
open MeasureTheory

namespace LambdaCantor.AE

def centeredNewtonFirstCoefficient (exponent : ℝ) (tailDepth depth : ℕ)
    (ratio firstPrefix : ℝ) : ℝ :=
  exponent * ratio ^ (tailDepth + depth) *
    (1 - ratio ^ tailDepth + ratio ^ tailDepth * firstPrefix) ^ (exponent - 1)

def centeredNewtonSecondCoefficient (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (ratio secondPrefix : ℝ) : ℝ :=
  exponent * ratio ^ (verticalDepth + tailDepth + depth) *
    (1 - ratio ^ verticalDepth + ratio ^ (verticalDepth + tailDepth) * secondPrefix) ^ (exponent - 1) /
      ratio ^ (exponent * horizontalDepth)

/-- The coefficient includes the full remaining-prefix scale. -/
theorem centeredNewtonFirstCoefficient_hasDerivAt (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (ratio firstPrefix secondPrefix : ℝ)
    (horizontal_positive : 0 < 1 - ratio ^ tailDepth + ratio ^ tailDepth * firstPrefix) :
    HasDerivAt
      (fun tail => centeredTailResidual exponent horizontalDepth verticalDepth tailDepth
        ratio (firstPrefix + ratio ^ depth * tail) secondPrefix)
      (centeredNewtonFirstCoefficient exponent tailDepth depth ratio firstPrefix) 0 := by
  have affine := ((hasDerivAt_id (0 : ℝ)).const_mul (ratio ^ depth)).const_add firstPrefix
  have horizontal := (affine.const_mul (ratio ^ tailDepth)).const_add (1 - ratio ^ tailDepth)
  have power := horizontal.rpow_const (p := exponent) (Or.inl (by simpa using horizontal_positive.ne'))
  convert! power.add_const
    (((1 - ratio ^ verticalDepth + ratio ^ (verticalDepth + tailDepth) * secondPrefix) ^ exponent - 1) /
      ratio ^ (exponent * horizontalDepth)) using 1 <;>
    simp [centeredTailResidual, centeredNewtonFirstCoefficient, pow_add,
      mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]

theorem centeredNewtonSecondCoefficient_hasDerivAt (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (ratio firstPrefix secondPrefix : ℝ)
    (vertical_positive :
      0 < 1 - ratio ^ verticalDepth + ratio ^ (verticalDepth + tailDepth) * secondPrefix) :
    HasDerivAt
      (fun tail => centeredTailResidual exponent horizontalDepth verticalDepth tailDepth
        ratio firstPrefix (secondPrefix + ratio ^ depth * tail))
      (centeredNewtonSecondCoefficient exponent horizontalDepth verticalDepth tailDepth depth ratio secondPrefix) 0 := by
  have affine := ((hasDerivAt_id (0 : ℝ)).const_mul (ratio ^ depth)).const_add secondPrefix
  have vertical := (affine.const_mul (ratio ^ (verticalDepth + tailDepth))).const_add (1 - ratio ^ verticalDepth)
  have power := vertical.rpow_const (p := exponent) (Or.inl (by simpa using vertical_positive.ne'))
  convert! ((power.sub_const 1).div_const (ratio ^ (exponent * horizontalDepth))).const_add
    ((1 - ratio ^ tailDepth + ratio ^ tailDepth * firstPrefix) ^ exponent) using 1 <;>
    simp [centeredTailResidual, centeredNewtonSecondCoefficient, pow_add,
      mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]

theorem centeredNewtonFirstCoefficient_positive {exponent ratio firstPrefix : ℝ}
    (tailDepth depth : ℕ) (exponent_positive : 0 < exponent) (ratio_positive : 0 < ratio)
    (horizontal_positive : 0 < 1 - ratio ^ tailDepth + ratio ^ tailDepth * firstPrefix) :
    0 < centeredNewtonFirstCoefficient exponent tailDepth depth ratio firstPrefix := by
  unfold centeredNewtonFirstCoefficient
  positivity

theorem centeredNewtonSecondCoefficient_positive {exponent ratio secondPrefix : ℝ}
    (horizontalDepth verticalDepth tailDepth depth : ℕ)
    (exponent_positive : 0 < exponent) (ratio_positive : 0 < ratio)
    (vertical_positive :
      0 < 1 - ratio ^ verticalDepth + ratio ^ (verticalDepth + tailDepth) * secondPrefix) :
    0 < centeredNewtonSecondCoefficient exponent horizontalDepth verticalDepth tailDepth depth ratio secondPrefix := by
  unfold centeredNewtonSecondCoefficient
  positivity

end LambdaCantor.AE
