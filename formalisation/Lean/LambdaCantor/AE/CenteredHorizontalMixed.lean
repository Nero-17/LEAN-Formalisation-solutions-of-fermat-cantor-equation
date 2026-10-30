import LambdaCantor.AE.CenteredResidual
import LambdaCantor.First.PrefixEstimates

noncomputable section
open Set

namespace LambdaCantor.AE

theorem power_derivative_product_difference_bound
    {exponent first second firstVelocity secondVelocity : ℝ}
    (exponent_greater_one : 1 < exponent)
    (first_mem : first ∈ Icc (1/2 : ℝ) 1) (second_mem : second ∈ Icc (1/2 : ℝ) 1) :
    |exponent * first^(exponent-1) * firstVelocity -
      exponent * second^(exponent-1) * secondVelocity| ≤
      exponent * |firstVelocity-secondVelocity| +
      (exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) *
        |first-second| * |secondVelocity| := by
  have exponent_positive : 0 < exponent := by linarith
  have exponent_minus_positive : 0 < exponent - 1 := sub_pos.mpr exponent_greater_one
  have coefficient_derivative : ∀ point ∈ Icc (1/2 : ℝ) 1,
      HasDerivAt (fun value : ℝ => exponent * value^(exponent-1))
        (centeredTaylorSecond exponent (1-point)) point := by
    intro point membership
    have positive : 0 < point := by linarith [membership.1]
    have model := ((hasDerivAt_id point).rpow_const (p := exponent-1)
      (Or.inl positive.ne')).const_mul exponent
    have hfunction := model.congr_of_eventuallyEq
      (f₁ := fun value : ℝ => exponent * value^(exponent-1))
      (Filter.Eventually.of_forall (fun _ => rfl))
    apply hfunction.congr_deriv
    simp only [centeredTaylorSecond, one_mul, id_eq,
      show exponent-1-1 = exponent-2 by ring, show 1-(1-point) = point by ring]
    ring
  have coefficient_difference := (convex_Icc (1/2 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun point membership => (coefficient_derivative point membership).differentiableAt)
    (fun point membership => by
      rw [(coefficient_derivative point membership).deriv]
      simpa only [Real.norm_eq_abs] using centeredTaylorSecond_bound exponent_greater_one
        (show 1-point ∈ Icc (0 : ℝ) (1/2) by constructor <;> linarith [membership.1, membership.2]))
    second_mem first_mem
  have first_coefficient : |exponent * first^(exponent-1)| ≤ exponent := by
    rw [abs_mul, abs_of_pos exponent_positive, abs_of_nonneg (Real.rpow_nonneg (by linarith [first_mem.1]) _)]
    exact mul_le_of_le_one_right exponent_positive.le
      (Real.rpow_le_one (by linarith [first_mem.1]) first_mem.2 (by linarith))
  have decomposition : exponent * first^(exponent-1) * firstVelocity -
      exponent * second^(exponent-1) * secondVelocity =
      (exponent * first^(exponent-1)) * (firstVelocity-secondVelocity) +
        (exponent * first^(exponent-1) - exponent * second^(exponent-1)) * secondVelocity := by ring
  rw [decomposition]
  apply (abs_add_le _ _).trans
  simp only [abs_mul]
  simp only [abs_mul] at first_coefficient
  exact add_le_add
    (mul_le_mul_of_nonneg_right first_coefficient (abs_nonneg _))
    (mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using coefficient_difference)
      (abs_nonneg _))

theorem centeredHorizontalFactor_parameter_hasDerivAt (tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1) :
    HasDerivAt (centeredHorizontalFactor tailDepth digits)
      ((tailDepth : ℝ)*ratio^(tailDepth-1)*(address ratio digits-1) +
        ratio^tailDepth*addressParameterDerivative ratio digits) ratio := by
  convert centeredHorizontalFactor_hasDerivAt tailDepth digits positive less_one using 1
  rw [(hasDerivAt_address_parameter positive less_one digits).deriv]
  ring

/-- The horizontal part of the actual mixed parameter/tail estimate. Shared
prefix cancellation is retained before estimating parameter derivatives. -/
theorem centered_horizontal_shared_prefix_derivative_bound
    {exponent ratio upper : ℝ} (exponent_greater_one : 1 < exponent)
    (positive : 0 < ratio) (ratio_upper : ratio ≤ upper) (upper_less_one : upper < 1)
    (tailDepth depth : ℕ) (tail_small : ratio^tailDepth ≤ 1/2)
    (first second : ℕ → Bool) (agreement : ∀ index < depth, first index = second index) :
    |deriv (fun parameter => (centeredHorizontalFactor tailDepth first parameter)^exponent) ratio -
      deriv (fun parameter => (centeredHorizontalFactor tailDepth second parameter)^exponent) ratio| ≤
      exponent *
        ((tailDepth : ℝ)*ratio^(tailDepth-1)*ratio^depth + ratio^tailDepth*
          ((depth : ℝ)*ratio^(depth-1) + 2*addressParameterDerivativeBound upper*ratio^depth)) +
      (exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) *
        (ratio^tailDepth*ratio^depth) *
        ((tailDepth : ℝ)*ratio^(tailDepth-1) + ratio^tailDepth*addressParameterDerivativeBound upper) := by
  have exponent_positive : 0 < exponent := by linarith
  have exponent_minus_positive : 0 < exponent - 1 := sub_pos.mpr exponent_greater_one
  have less_one := ratio_upper.trans_lt upper_less_one
  have tail_coefficient_nonnegative : 0 ≤ (tailDepth : ℝ)*ratio^(tailDepth-1) :=
    mul_nonneg (Nat.cast_nonneg (α := ℝ) tailDepth) (pow_nonneg positive.le _)
  have address_bounds (digits : ℕ → Bool) : address ratio digits ∈ Icc (0 : ℝ) 1 :=
    cantorSet_subset_unitInterval positive.le less_one ⟨digits, rfl⟩
  have horizontal_bounds (digits : ℕ → Bool) : centeredHorizontalFactor tailDepth digits ratio ∈ Icc (1/2 : ℝ) 1 := by
    have bounds := address_bounds digits
    unfold centeredHorizontalFactor
    constructor
    · nlinarith [mul_nonneg (pow_nonneg positive.le tailDepth) bounds.1]
    · nlinarith [mul_le_mul_of_nonneg_left bounds.2 (pow_nonneg positive.le tailDepth)]
  have horizontal_difference :
      |centeredHorizontalFactor tailDepth first ratio - centeredHorizontalFactor tailDepth second ratio| ≤
        ratio^tailDepth*ratio^depth := by
    have difference := address_shared_prefix_bound positive.le less_one first second depth agreement
    have identity : centeredHorizontalFactor tailDepth first ratio - centeredHorizontalFactor tailDepth second ratio =
      ratio^tailDepth * (address ratio first-address ratio second) := by unfold centeredHorizontalFactor; ring
    rw [identity, abs_mul, abs_of_nonneg (pow_nonneg positive.le tailDepth)]
    exact mul_le_mul_of_nonneg_left difference (pow_nonneg positive.le tailDepth)
  have velocity_difference :
      |((tailDepth : ℝ)*ratio^(tailDepth-1)*(address ratio first-1) +
        ratio^tailDepth*addressParameterDerivative ratio first) -
       ((tailDepth : ℝ)*ratio^(tailDepth-1)*(address ratio second-1) +
        ratio^tailDepth*addressParameterDerivative ratio second)| ≤
      (tailDepth : ℝ)*ratio^(tailDepth-1)*ratio^depth + ratio^tailDepth*
        ((depth : ℝ)*ratio^(depth-1) + 2*addressParameterDerivativeBound upper*ratio^depth) := by
    have identity :
      ((tailDepth : ℝ)*ratio^(tailDepth-1)*(address ratio first-1) +
        ratio^tailDepth*addressParameterDerivative ratio first) -
       ((tailDepth : ℝ)*ratio^(tailDepth-1)*(address ratio second-1) +
        ratio^tailDepth*addressParameterDerivative ratio second) =
      (tailDepth : ℝ)*ratio^(tailDepth-1)*(address ratio first-address ratio second) +
        ratio^tailDepth*(addressParameterDerivative ratio first-addressParameterDerivative ratio second) := by ring
    rw [identity]
    apply (abs_add_le _ _).trans
    simp only [abs_mul, Nat.abs_cast,
      abs_of_nonneg (pow_nonneg positive.le (tailDepth-1)),
      abs_of_nonneg (pow_nonneg positive.le tailDepth)]
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (address_shared_prefix_bound positive.le less_one first second depth agreement)
        tail_coefficient_nonnegative)
      (mul_le_mul_of_nonneg_left
        (address_shared_prefix_derivative_bound positive ratio_upper upper_less_one first second depth agreement)
        (pow_nonneg positive.le tailDepth))
  have second_velocity :
      |(tailDepth : ℝ)*ratio^(tailDepth-1)*(address ratio second-1) +
        ratio^tailDepth*addressParameterDerivative ratio second| ≤
      (tailDepth : ℝ)*ratio^(tailDepth-1) + ratio^tailDepth*addressParameterDerivativeBound upper := by
    apply (abs_add_le _ _).trans
    simp only [abs_mul, Nat.abs_cast,
      abs_of_nonneg (pow_nonneg positive.le (tailDepth-1)),
      abs_of_nonneg (pow_nonneg positive.le tailDepth)]
    have displacement : |address ratio second-1| ≤ 1 := by
      rw [abs_of_nonpos (by linarith [(address_bounds second).2])]
      linarith [(address_bounds second).1]
    exact add_le_add
      (mul_le_of_le_one_right tail_coefficient_nonnegative displacement)
      (mul_le_mul_of_nonneg_left
        (address_parameter_derivative_bound positive.le ratio_upper upper_less_one second)
        (pow_nonneg positive.le tailDepth))
  have first_derivative := (centeredHorizontalFactor_parameter_hasDerivAt tailDepth first positive less_one).rpow_const
    (p := exponent) (Or.inl (by linarith [(horizontal_bounds first).1]))
  have second_derivative := (centeredHorizontalFactor_parameter_hasDerivAt tailDepth second positive less_one).rpow_const
    (p := exponent) (Or.inl (by linarith [(horizontal_bounds second).1]))
  rw [first_derivative.deriv, second_derivative.deriv]
  have estimate := power_derivative_product_difference_bound exponent_greater_one
    (horizontal_bounds first) (horizontal_bounds second)
    (firstVelocity := (tailDepth : ℝ)*ratio^(tailDepth-1)*(address ratio first-1) +
      ratio^tailDepth*addressParameterDerivative ratio first)
    (secondVelocity := (tailDepth : ℝ)*ratio^(tailDepth-1)*(address ratio second-1) +
      ratio^tailDepth*addressParameterDerivative ratio second)
  have reordered :
      |(((tailDepth : ℝ)*ratio^(tailDepth-1)*(address ratio first-1) +
        ratio^tailDepth*addressParameterDerivative ratio first)*exponent*
        (centeredHorizontalFactor tailDepth first ratio)^(exponent-1)) -
       (((tailDepth : ℝ)*ratio^(tailDepth-1)*(address ratio second-1) +
        ratio^tailDepth*addressParameterDerivative ratio second)*exponent*
        (centeredHorizontalFactor tailDepth second ratio)^(exponent-1))| =
      |exponent * (centeredHorizontalFactor tailDepth first ratio)^(exponent-1) *
          ((tailDepth : ℝ)*ratio^(tailDepth-1)*(address ratio first-1) +
            ratio^tailDepth*addressParameterDerivative ratio first) -
        exponent * (centeredHorizontalFactor tailDepth second ratio)^(exponent-1) *
          ((tailDepth : ℝ)*ratio^(tailDepth-1)*(address ratio second-1) +
            ratio^tailDepth*addressParameterDerivative ratio second)| := by
    congr 1
    ring
  rw [reordered]
  apply estimate.trans
  apply add_le_add (mul_le_mul_of_nonneg_left velocity_difference exponent_positive.le)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left horizontal_difference (by positivity)) second_velocity
    (abs_nonneg _) (by positivity)

end LambdaCantor.AE
