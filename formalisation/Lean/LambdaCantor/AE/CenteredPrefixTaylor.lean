import LambdaCantor.AE.PrefixTailGeometry
import LambdaCantor.AE.NewtonMixture
import LambdaCantor.AE.CenteredTailRemainder
import LambdaCantor.AE.CenteredPrefixLipschitz

noncomputable section
open Set

namespace LambdaCantor.AE

theorem centeredPrefixBaseline_eq_normalized (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (digits : ℕ → Bool × Bool)
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1) :
    centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth (fun index => digits index) ratio =
      centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth (pairedZeroPrefixDigits depth digits) ratio := by
  rw [centered_residual_scalar_formula exponent horizontalDepth verticalDepth tailDepth
    (pairedZeroPrefixDigits depth digits) positive less_one]
  unfold centeredPrefixBaseline centeredTailResidual pairedZeroPrefixDigits zeroPrefixDigits
  rfl

theorem centered_residual_actual_prefix_tails (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (digits : ℕ → Bool × Bool)
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1) :
    centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits ratio =
      centeredTailResidual exponent horizontalDepth verticalDepth tailDepth ratio
        (address ratio (zeroPrefixDigits depth (fun index => (digits index).1)) +
          ratio^depth*address ratio (fun index => (digits (index+depth)).1))
        (address ratio (zeroPrefixDigits depth (fun index => (digits index).2)) +
          ratio^depth*address ratio (fun index => (digits (index+depth)).2)) := by
  rw [centered_residual_scalar_formula exponent horizontalDepth verticalDepth tailDepth digits positive less_one]
  unfold centeredTailResidual
  rw [address_prefix_zero_tail positive.le less_one (fun index => (digits index).1) depth,
    address_prefix_zero_tail positive.le less_one (fun index => (digits index).2) depth]

/-- The genuine prefix addresses satisfy the lower and upper base-coordinate
conditions needed by the real-tail Taylor theorem. -/
theorem centered_prefix_base_bounds
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1)
    (verticalDepth tailDepth depth : ℕ) (digits : ℕ → Bool × Bool)
    (tail_small : ratio^tailDepth ≤ 1/2) (vertical_small : ratio^verticalDepth ≤ 1/2) :
    (1/2 ≤ 1-ratio^tailDepth+ratio^tailDepth*address ratio (zeroPrefixDigits depth (fun index => (digits index).1))) ∧
    (1-ratio^tailDepth+ratio^tailDepth*address ratio (zeroPrefixDigits depth (fun index => (digits index).1))+
      ratio^(tailDepth+depth) ≤ 1) ∧
    (1/2 ≤ 1-ratio^verticalDepth+ratio^(verticalDepth+tailDepth)*address ratio (zeroPrefixDigits depth (fun index => (digits index).2))) ∧
    (1-ratio^verticalDepth+ratio^(verticalDepth+tailDepth)*address ratio (zeroPrefixDigits depth (fun index => (digits index).2))+
      ratio^(verticalDepth+tailDepth+depth) ≤ 1) := by
  have first := address_zeroPrefixDigits_bounds positive.le less_one (fun index => (digits index).1) depth
  have second := address_zeroPrefixDigits_bounds positive.le less_one (fun index => (digits index).2) depth
  have tail_nonnegative := pow_nonneg positive.le tailDepth
  have vertical_nonnegative := pow_nonneg positive.le verticalDepth
  have tail_one := pow_le_one₀ positive.le less_one.le (n := tailDepth)
  have horizontal_product := mul_le_mul_of_nonneg_left first.2 tail_nonnegative
  have vertical_product := mul_le_mul_of_nonneg_left second.2
    (mul_nonneg vertical_nonnegative tail_nonnegative)
  have vertical_tail := mul_le_mul_of_nonneg_left tail_one vertical_nonnegative
  simp only [pow_add] at horizontal_product vertical_product vertical_tail ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg tail_nonnegative first.1]
  · nlinarith
  · nlinarith [mul_nonneg (mul_nonneg vertical_nonnegative tail_nonnegative) second.1]
  · nlinarith

/-- Actual frozen-tail error for the actual prefix of an arbitrary address,
with the precise Newton residual and both actual affine coefficients. -/
theorem centered_frozen_actual_tail_remainder
    {exponent ratio : ℝ} (exponent_greater_one : 1 < exponent)
    (positive : 0 < ratio) (less_one : ratio < 1)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (digits : ℕ → Bool × Bool)
    (tail_small : ratio^tailDepth ≤ 1/2) (vertical_small : ratio^verticalDepth ≤ 1/2) :
    |centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits ratio -
      (centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth (fun index => digits index) ratio).residual -
      (centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth (fun index => digits index) ratio).firstCoefficient *
        address ratio (fun index => (digits (index+depth)).1) -
      (centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth (fun index => digits index) ratio).secondCoefficient *
        address ratio (fun index => (digits (index+depth)).2)| ≤
      (exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) *
        ((ratio^(tailDepth+depth))^2+(ratio^(verticalDepth+tailDepth+depth))^2/ratio^(exponent*horizontalDepth)) := by
  have bases := centered_prefix_base_bounds positive less_one verticalDepth tailDepth depth digits tail_small vertical_small
  have first_tail : address ratio (fun index => (digits (index+depth)).1) ∈ Icc (0 : ℝ) 1 :=
    cantorSet_subset_unitInterval positive.le less_one ⟨_, rfl⟩
  have second_tail : address ratio (fun index => (digits (index+depth)).2) ∈ Icc (0 : ℝ) 1 :=
    cantorSet_subset_unitInterval positive.le less_one ⟨_, rfl⟩
  have estimate := centeredTailResidual_tail_remainder_bound horizontalDepth verticalDepth tailDepth depth
    exponent_greater_one positive bases.1 bases.2.1 bases.2.2.1 bases.2.2.2 first_tail second_tail
  rw [centered_residual_actual_prefix_tails exponent horizontalDepth verticalDepth tailDepth depth digits positive less_one]
  have prefix_address (coordinate : ℕ → Bool) :
      address ratio (zeroPrefixDigits depth coordinate) =
        address ratio (fun index => if index < depth then coordinate index else false) := by
    apply congrArg (address ratio)
    funext index
    rfl
  simpa only [centeredFrozenNewton, centeredPrefixBaseline, prefix_address, dite_eq_ite] using estimate

theorem centered_tail_remainder_scale_bound
    {exponent ratio upper rho bound normalizedBound : ℝ}
    (positive : 0 < ratio) (ratio_upper : ratio ≤ upper) (rho_nonnegative : 0 ≤ rho)
    (bound_nonnegative : 0 ≤ bound) (horizontalDepth verticalDepth tailDepth depth : ℕ)
    (vertical_large : 1 ≤ verticalDepth) (tail_rho : ratio^tailDepth ≤ 2*rho)
    (normalized_bound : (verticalDepth : ℝ)^2*
      (ratio^(-exponent*(horizontalDepth : ℝ))*(ratio^verticalDepth)^2) ≤ normalizedBound) :
    bound*((ratio^(tailDepth+depth))^2+(ratio^(verticalDepth+tailDepth+depth))^2/ratio^(exponent*horizontalDepth)) ≤
      4*bound*(1+normalizedBound)*rho^2*(upper^depth)^2 := by
  have upper_positive := positive.trans_le ratio_upper
  have normalized_nonnegative : 0 ≤ ratio^(-exponent*(horizontalDepth : ℝ))*(ratio^verticalDepth)^2 := by positivity
  have vertical_ge_one : (1 : ℝ) ≤ verticalDepth := by exact_mod_cast vertical_large
  have vertical_square : (1 : ℝ) ≤ (verticalDepth : ℝ)^2 := by nlinarith
  have normalization_bound : ratio^(-exponent*(horizontalDepth : ℝ))*(ratio^verticalDepth)^2 ≤ normalizedBound :=
    (le_mul_of_one_le_left normalized_nonnegative vertical_square).trans normalized_bound
  have normalizedBound_nonnegative := normalized_nonnegative.trans normalization_bound
  have inverse_identity : ratio^(-exponent*(horizontalDepth : ℝ)) = (ratio^(exponent*horizontalDepth))⁻¹ := by
    rw [show -exponent*(horizontalDepth : ℝ) = -(exponent*horizontalDepth) by ring, Real.rpow_neg positive.le]
  have identity :
      bound*((ratio^(tailDepth+depth))^2+(ratio^(verticalDepth+tailDepth+depth))^2/ratio^(exponent*horizontalDepth)) =
        (bound*(1+ratio^(-exponent*(horizontalDepth : ℝ))*(ratio^verticalDepth)^2)) *
          (ratio^tailDepth)^2*(ratio^depth)^2 := by
    rw [pow_add ratio tailDepth depth, pow_add ratio (verticalDepth+tailDepth) depth,
      pow_add ratio verticalDepth tailDepth, div_eq_mul_inv, ← inverse_identity]
    ring
  rw [identity]
  have coefficient := mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) normalization_bound) bound_nonnegative
  have tail_square := pow_le_pow_left₀ (pow_nonneg positive.le tailDepth) tail_rho 2
  have depth_square := pow_le_pow_left₀ (pow_nonneg positive.le depth)
    (pow_le_pow_left₀ positive.le ratio_upper depth) 2
  have product := mul_le_mul
    (mul_le_mul coefficient tail_square (sq_nonneg (ratio^tailDepth)) (by positivity))
      depth_square (sq_nonneg (ratio^depth)) (by positivity)
  apply product.trans_eq
  ring

theorem centered_frozen_actual_tail_rho_remainder
    {exponent ratio upper rho normalizedBound : ℝ} (exponent_greater_one : 1 < exponent)
    (positive : 0 < ratio) (less_one : ratio < 1) (ratio_upper : ratio ≤ upper) (rho_nonnegative : 0 ≤ rho)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (digits : ℕ → Bool × Bool)
    (vertical_large : 1 ≤ verticalDepth) (tail_small : ratio^tailDepth ≤ 1/2) (vertical_small : ratio^verticalDepth ≤ 1/2)
    (tail_rho : ratio^tailDepth ≤ 2*rho)
    (normalized_bound : (verticalDepth : ℝ)^2*
      (ratio^(-exponent*(horizontalDepth : ℝ))*(ratio^verticalDepth)^2) ≤ normalizedBound) :
    |centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits ratio -
      (centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth (fun index => digits index) ratio).residual -
      (centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth (fun index => digits index) ratio).firstCoefficient *
        address ratio (fun index => (digits (index+depth)).1) -
      (centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth (fun index => digits index) ratio).secondCoefficient *
        address ratio (fun index => (digits (index+depth)).2)| ≤
      4*(exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2)))*(1+normalizedBound)*rho^2*(upper^depth)^2 := by
  have exponent_positive : 0 < exponent := by linarith
  have exponent_minus_positive : 0 < exponent-1 := sub_pos.mpr exponent_greater_one
  apply (centered_frozen_actual_tail_remainder exponent_greater_one positive less_one horizontalDepth verticalDepth tailDepth depth
    digits tail_small vertical_small).trans
  exact centered_tail_remainder_scale_bound positive ratio_upper rho_nonnegative (by positivity)
    horizontalDepth verticalDepth tailDepth depth vertical_large tail_rho normalized_bound

end LambdaCantor.AE
