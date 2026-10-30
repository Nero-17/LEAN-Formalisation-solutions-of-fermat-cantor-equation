import LambdaCantor.SelfSimilarity
import LambdaCantor.First.AddressParameter
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
namespace LambdaCantor.First.Roots

/-- Affine frozen kernel evaluated on two unrestricted full Cantor tails. -/
def frozenKernel (ratio centre horizontal vertical : ℝ)
    (left right : ℕ → Bool) : ℝ :=
  centre - horizontal * address ratio left - vertical * address ratio right

/-- Exact four-way splitting of the complete frozen kernel. No tail restriction
appears: this is the identity prior to deletion of children missing the compact set. -/
theorem frozenKernel_first_digits {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (centre horizontal vertical : ℝ)
    (leftDigit rightDigit : Bool) (left right : ℕ → Bool) :
    frozenKernel ratio centre horizontal vertical
      (prependDigit leftDigit left) (prependDigit rightDigit right) =
    frozenKernel ratio
      (centre - horizontal * (1 - ratio) * (if leftDigit then 1 else 0) -
        vertical * (1 - ratio) * (if rightDigit then 1 else 0))
      (ratio * horizontal) (ratio * vertical) left right := by
  unfold frozenKernel
  rw [address_prepend nonnegative less_one, address_prepend nonnegative less_one]
  ring

/-- The source root-kernel formula is an unrestricted affine frozen kernel. -/
theorem root_kernel_as_frozen (exponent ratio x y derivative leftTail rightTail : ℝ)
    (horizontalDepth verticalDepth depth : ℕ) (left right : ℕ → Bool) :
    ratio - (exponent * x ^ (exponent - 1) * ratio ^ (horizontalDepth + depth) / derivative) *
        (address ratio left - leftTail) -
      (exponent * y ^ (exponent - 1) * ratio ^ (verticalDepth + depth) / derivative) *
        (address ratio right - rightTail) =
    frozenKernel ratio
      (ratio + (exponent * x ^ (exponent - 1) * ratio ^ (horizontalDepth + depth) / derivative) * leftTail +
        (exponent * y ^ (exponent - 1) * ratio ^ (verticalDepth + depth) / derivative) * rightTail)
      (exponent * x ^ (exponent - 1) * ratio ^ (horizontalDepth + depth) / derivative)
      (exponent * y ^ (exponent - 1) * ratio ^ (verticalDepth + depth) / derivative) left right := by
  unfold frozenKernel
  ring

/-- Direct coupling of complete frozen kernels with the same paired tail.
Parameter variation is controlled by the proved address derivative bound. -/
theorem frozenKernel_displacement {lower upper leftRatio rightRatio : ℝ}
    (lower_pos : 0 < lower) (upper_lt_one : upper < 1)
    (left_in_band : leftRatio ∈ Set.Icc lower upper)
    (right_in_band : rightRatio ∈ Set.Icc lower upper)
    (leftCentre rightCentre leftHorizontal rightHorizontal leftVertical rightVertical : ℝ)
    (left right : ℕ → Bool) :
    |frozenKernel leftRatio leftCentre leftHorizontal leftVertical left right -
      frozenKernel rightRatio rightCentre rightHorizontal rightVertical left right| ≤
      |leftCentre - rightCentre| + |leftHorizontal - rightHorizontal| +
        |leftVertical - rightVertical| +
        (|rightHorizontal| + |rightVertical|) * addressParameterDerivativeBound upper *
          |leftRatio - rightRatio| := by
  have coordinate_bound (digits : ℕ → Bool) (first second : ℝ) :
      |first * address leftRatio digits - second * address rightRatio digits| ≤
        |first - second| + |second| *
          (addressParameterDerivativeBound upper * |leftRatio - rightRatio|) := by
    have identity : first * address leftRatio digits - second * address rightRatio digits =
        (first - second) * address leftRatio digits +
          second * (address leftRatio digits - address rightRatio digits) := by ring
    have address_nonnegative := address_nonnegative (lower_pos.le.trans left_in_band.1)
      (left_in_band.2.trans_lt upper_lt_one) digits
    have address_upper := address_le_one (lower_pos.le.trans left_in_band.1)
      (left_in_band.2.trans_lt upper_lt_one) digits
    have parameter_bound := address_parameter_lipschitz_estimate lower_pos upper_lt_one
      right_in_band left_in_band digits
    rw [identity]
    calc
      _ ≤ |(first - second) * address leftRatio digits| +
          |second * (address leftRatio digits - address rightRatio digits)| := abs_add_le _ _
      _ = |first - second| * address leftRatio digits +
          |second| * |address leftRatio digits - address rightRatio digits| := by
            rw [abs_mul, abs_mul, abs_of_nonneg address_nonnegative]
      _ ≤ |first - second| * 1 + |second| *
          (addressParameterDerivativeBound upper * |leftRatio - rightRatio|) :=
        add_le_add (mul_le_mul_of_nonneg_left address_upper (abs_nonneg _))
          (mul_le_mul_of_nonneg_left parameter_bound (abs_nonneg _))
      _ = _ := by ring
  have identity :
      frozenKernel leftRatio leftCentre leftHorizontal leftVertical left right -
        frozenKernel rightRatio rightCentre rightHorizontal rightVertical left right =
      (leftCentre - rightCentre) -
        (leftHorizontal * address leftRatio left - rightHorizontal * address rightRatio left) -
        (leftVertical * address leftRatio right - rightVertical * address rightRatio right) := by
    unfold frozenKernel
    ring
  rw [identity]
  have first_triangle := abs_sub (leftCentre - rightCentre)
    (leftHorizontal * address leftRatio left - rightHorizontal * address rightRatio left)
  have second_triangle := abs_sub
    (leftCentre - rightCentre -
      (leftHorizontal * address leftRatio left - rightHorizontal * address rightRatio left))
    (leftVertical * address leftRatio right - rightVertical * address rightRatio right)
  have horizontal_bound := coordinate_bound left leftHorizontal rightHorizontal
  have vertical_bound := coordinate_bound right leftVertical rightVertical
  nlinarith

end LambdaCantor.First.Roots
