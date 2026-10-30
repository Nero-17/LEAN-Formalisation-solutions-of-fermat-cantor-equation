import LambdaCantor.AE.NewtonRemainder
import LambdaCantor.AE.CenteredNewtonCoefficients

noncomputable section
open Set

namespace LambdaCantor.AE

/-- The actual power nonlinearity on the centered cylinders has a uniform
quadratic tail remainder, including real exponents between one and two. -/
theorem affine_power_tail_remainder_bound {exponent base scale tail : ℝ}
    (exponent_greater_one : 1 < exponent) (base_lower : 1/2 ≤ base)
    (scale_nonnegative : 0 ≤ scale) (endpoint_upper : base + scale ≤ 1)
    (tail_mem : tail ∈ Icc (0 : ℝ) 1) :
    |(base + scale * tail)^exponent - base^exponent -
      (exponent * scale * base^(exponent - 1)) * tail| ≤
      (exponent * (exponent - 1) * max 1 ((1/2 : ℝ)^(exponent - 2))) * scale^2 := by
  have exponent_positive : 0 < exponent := by linarith
  have exponent_minus_positive : 0 < exponent - 1 := sub_pos.mpr exponent_greater_one
  have constant_nonnegative :
      0 ≤ exponent * (exponent - 1) * max 1 ((1/2 : ℝ)^(exponent - 2)) := by positivity
  have base_bounds : ∀ parameter ∈ uIcc (0 : ℝ) tail,
      base + scale * parameter ∈ Icc (1/2 : ℝ) 1 := by
    intro parameter membership
    rw [uIcc_of_le tail_mem.1] at membership
    have parameter_upper : parameter ≤ 1 := membership.2.trans tail_mem.2
    constructor
    · nlinarith [mul_nonneg scale_nonnegative membership.1]
    · nlinarith [mul_le_mul_of_nonneg_left parameter_upper scale_nonnegative]
  have first_derivative : ∀ parameter ∈ uIcc (0 : ℝ) tail,
      HasDerivAt (fun value : ℝ => (base + scale * value)^exponent)
        (exponent * scale * (base + scale * parameter)^(exponent - 1)) parameter := by
    intro parameter membership
    have positive : 0 < base + scale * parameter := by linarith [(base_bounds parameter membership).1]
    apply (((((hasDerivAt_id parameter).const_mul scale).const_add base).rpow_const
      (p := exponent) (Or.inl positive.ne')).congr_of_eventuallyEq
        (f₁ := fun value : ℝ => (base + scale * value)^exponent)
        (Filter.Eventually.of_forall (fun _ => rfl))).congr_deriv
    (try simp only [id_eq, mul_one]) <;> ring
  have second_derivative : ∀ parameter ∈ uIcc (0 : ℝ) tail,
      HasDerivAt (fun value : ℝ => exponent * scale * (base + scale * value)^(exponent - 1))
        (scale^2 * (exponent * (exponent - 1) * (base + scale * parameter)^(exponent - 2))) parameter := by
    intro parameter membership
    have positive : 0 < base + scale * parameter := by linarith [(base_bounds parameter membership).1]
    have derivative := ((((hasDerivAt_id parameter).const_mul scale).const_add base).rpow_const
      (p := exponent - 1) (Or.inl positive.ne')).const_mul (exponent * scale)
    apply (derivative.congr_of_eventuallyEq
      (f₁ := fun value : ℝ => exponent * scale * (base + scale * value)^(exponent - 1))
      (Filter.Eventually.of_forall (fun _ => rfl))).congr_deriv
    (try simp only [id_eq, show exponent - 1 - 1 = exponent - 2 by ring, mul_one]) <;> ring
  have second_bound : ∀ parameter ∈ uIcc (0 : ℝ) tail,
      |scale^2 * (exponent * (exponent - 1) * (base + scale * parameter)^(exponent - 2))| ≤
        (exponent * (exponent - 1) * max 1 ((1/2 : ℝ)^(exponent - 2))) * scale^2 := by
    intro parameter membership
    have bounds := base_bounds parameter membership
    have bound := centeredTaylorSecond_bound exponent_greater_one
      (show 1 - (base + scale * parameter) ∈ Icc (0 : ℝ) (1/2) by
        constructor <;> linarith [bounds.1, bounds.2])
    have identity : 1 - (1 - (base + scale * parameter)) = base + scale * parameter := by ring
    simp only [centeredTaylorSecond, identity] at bound
    rw [abs_mul, abs_of_nonneg (sq_nonneg scale)]
    exact (mul_le_mul_of_nonneg_left bound (sq_nonneg scale)).trans_eq (mul_comm _ _)
  have remainder := first_order_remainder_bound
    (fun value : ℝ => (base + scale * value)^exponent)
    (fun value : ℝ => exponent * scale * (base + scale * value)^(exponent - 1))
    (fun value : ℝ => scale^2 * (exponent * (exponent - 1) * (base + scale * value)^(exponent - 2)))
    (mul_nonneg constant_nonnegative (sq_nonneg scale))
    first_derivative second_derivative second_bound
  simp only [mul_zero, add_zero, sub_zero] at remainder
  apply remainder.trans
  have tail_square : |tail|^2 ≤ 1 := by
    rw [sq_abs]
    nlinarith [tail_mem.1, tail_mem.2]
  exact (mul_le_mul_of_nonneg_left tail_square
    (mul_nonneg constant_nonnegative (sq_nonneg scale))).trans_eq (mul_one _)

/-- Both real-tail Taylor errors for the exact centered residual. Prefixes
enter only through the actual horizontal and vertical base coordinates. -/
theorem centeredTailResidual_tail_remainder_bound
    {exponent ratio firstPrefix secondPrefix firstTail secondTail : ℝ}
    (horizontalDepth verticalDepth tailDepth depth : ℕ)
    (exponent_greater_one : 1 < exponent) (ratio_positive : 0 < ratio)
    (horizontal_lower : 1/2 ≤ 1 - ratio^tailDepth + ratio^tailDepth * firstPrefix)
    (horizontal_upper : 1 - ratio^tailDepth + ratio^tailDepth * firstPrefix + ratio^(tailDepth + depth) ≤ 1)
    (vertical_lower : 1/2 ≤ 1 - ratio^verticalDepth + ratio^(verticalDepth + tailDepth) * secondPrefix)
    (vertical_upper : 1 - ratio^verticalDepth + ratio^(verticalDepth + tailDepth) * secondPrefix +
      ratio^(verticalDepth + tailDepth + depth) ≤ 1)
    (first_tail : firstTail ∈ Icc (0 : ℝ) 1) (second_tail : secondTail ∈ Icc (0 : ℝ) 1) :
    |centeredTailResidual exponent horizontalDepth verticalDepth tailDepth ratio
        (firstPrefix + ratio^depth * firstTail) (secondPrefix + ratio^depth * secondTail) -
      centeredTailResidual exponent horizontalDepth verticalDepth tailDepth ratio firstPrefix secondPrefix -
      centeredNewtonFirstCoefficient exponent tailDepth depth ratio firstPrefix * firstTail -
      centeredNewtonSecondCoefficient exponent horizontalDepth verticalDepth tailDepth depth ratio secondPrefix * secondTail| ≤
      (exponent * (exponent - 1) * max 1 ((1/2 : ℝ)^(exponent - 2))) *
        ((ratio^(tailDepth + depth))^2 +
          (ratio^(verticalDepth + tailDepth + depth))^2 / ratio^(exponent * horizontalDepth)) := by
  have horizontal := affine_power_tail_remainder_bound exponent_greater_one horizontal_lower
    (pow_nonneg ratio_positive.le _) horizontal_upper first_tail
  have vertical := affine_power_tail_remainder_bound exponent_greater_one vertical_lower
    (pow_nonneg ratio_positive.le _) vertical_upper second_tail
  have denominator_positive := Real.rpow_pos_of_pos ratio_positive (exponent * horizontalDepth)
  have decomposition :
      centeredTailResidual exponent horizontalDepth verticalDepth tailDepth ratio
        (firstPrefix + ratio^depth * firstTail) (secondPrefix + ratio^depth * secondTail) -
      centeredTailResidual exponent horizontalDepth verticalDepth tailDepth ratio firstPrefix secondPrefix -
      centeredNewtonFirstCoefficient exponent tailDepth depth ratio firstPrefix * firstTail -
      centeredNewtonSecondCoefficient exponent horizontalDepth verticalDepth tailDepth depth ratio secondPrefix * secondTail =
      ((1 - ratio^tailDepth + ratio^tailDepth * firstPrefix + ratio^(tailDepth + depth) * firstTail)^exponent -
        (1 - ratio^tailDepth + ratio^tailDepth * firstPrefix)^exponent -
        (exponent * ratio^(tailDepth + depth) *
          (1 - ratio^tailDepth + ratio^tailDepth * firstPrefix)^(exponent - 1)) * firstTail) +
      (((1 - ratio^verticalDepth + ratio^(verticalDepth + tailDepth) * secondPrefix +
          ratio^(verticalDepth + tailDepth + depth) * secondTail)^exponent -
        (1 - ratio^verticalDepth + ratio^(verticalDepth + tailDepth) * secondPrefix)^exponent -
        (exponent * ratio^(verticalDepth + tailDepth + depth) *
          (1 - ratio^verticalDepth + ratio^(verticalDepth + tailDepth) * secondPrefix)^(exponent - 1)) * secondTail) /
        ratio^(exponent * horizontalDepth)) := by
    unfold centeredTailResidual centeredNewtonFirstCoefficient centeredNewtonSecondCoefficient
    have horizontal_identity :
        1 - ratio^tailDepth + ratio^tailDepth * (firstPrefix + ratio^depth * firstTail) =
        1 - ratio^tailDepth + ratio^tailDepth * firstPrefix + ratio^(tailDepth + depth) * firstTail := by
      rw [pow_add]
      ring
    have vertical_identity :
        1 - ratio^verticalDepth + ratio^(verticalDepth + tailDepth) * (secondPrefix + ratio^depth * secondTail) =
        1 - ratio^verticalDepth + ratio^(verticalDepth + tailDepth) * secondPrefix +
          ratio^(verticalDepth + tailDepth + depth) * secondTail := by
      rw [pow_add ratio (verticalDepth + tailDepth) depth]
      ring
    rw [horizontal_identity, vertical_identity]
    ring
  rw [decomposition]
  apply (abs_add_le _ _).trans
  rw [abs_div, abs_of_pos denominator_positive]
  apply (add_le_add horizontal (div_le_div_of_nonneg_right vertical denominator_positive.le)).trans_eq
  ring

end LambdaCantor.AE
