import LambdaCantor.AE.CenteredDisplacementSecond
import Lean.Elab.Tactic.Omega

noncomputable section
namespace LambdaCantor.AE

/-- A fixed number of derivatives costs only the corresponding inverse power
of the lower endpoint of a compact parameter interval. -/
theorem centered_shifted_power_bound {lower ratio upper : ℝ}
    (hlower : 0 < lower) (hratio : lower ≤ ratio) (hupper : ratio ≤ upper)
    (depth offset : ℕ) (hdepth : offset ≤ depth) :
    ratio ^ (depth - offset) ≤ upper ^ depth / lower ^ offset := by
  apply (le_div_iff₀ (pow_pos hlower offset)).mpr
  calc
    ratio ^ (depth - offset) * lower ^ offset ≤
        ratio ^ (depth - offset) * ratio ^ offset :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlower.le hratio offset)
        (pow_nonneg (hlower.le.trans hratio) (depth - offset))
    _ = ratio ^ depth := by rw [← pow_add, Nat.sub_add_cancel hdepth]
    _ ≤ upper ^ depth := pow_le_pow_left₀ (hlower.le.trans hratio) hupper depth

/-- All cylinder depths appearing after two differentiations are controlled
by the same exponential factor, including the deeper tail cylinder. -/
theorem centered_tail_shifted_power_bound {lower ratio upper : ℝ}
    (hlower : 0 < lower) (hratio : lower ≤ ratio) (hupper : ratio ≤ upper)
    (hless : upper < 1) (depth tailDepth offset : ℕ) (hdepth : offset ≤ depth) :
    ratio ^ (depth + tailDepth - offset) ≤ upper ^ depth / lower ^ offset := by
  apply (centered_shifted_power_bound hlower hratio hupper
    (depth + tailDepth) offset (by omega)).trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg hlower.le offset)
  exact pow_le_pow_of_le_one (hlower.le.trans (hratio.trans hupper)) hless.le (by omega)

theorem centeredDisplacement_first_uniform_bound
    {lower ratio upper firstBound : ℝ} (hlower : 0 < lower)
    (hratio : lower ≤ ratio) (hupper : ratio ≤ upper) (hless : upper < 1)
    (depth tailDepth : ℕ) (hdepth : 1 ≤ depth) (digits : ℕ → Bool)
    (hfirst : |deriv (fun parameter => address parameter digits) ratio| ≤ firstBound) :
    |centeredDisplacementFirst depth tailDepth digits ratio| ≤
      (depth : ℝ) * (upper ^ depth / lower) +
        ((depth + tailDepth : ℕ) : ℝ) * (upper ^ depth / lower) +
          upper ^ depth * firstBound := by
  have hpositive := hlower.trans_le hratio
  have haddress := cantorSet_subset_unitInterval hpositive.le (hupper.trans_lt hless)
    (show address ratio digits ∈ cantorSet ratio from ⟨digits, rfl⟩)
  have haddressNonnegative := haddress.1
  have hshift := centered_shifted_power_bound hlower hratio hupper depth 1 hdepth
  have htail := centered_tail_shifted_power_bound hlower hratio hupper hless depth tailDepth 1 hdepth
  have hpower := centered_tail_shifted_power_bound hlower hratio hupper hless depth tailDepth 0 (by omega)
  simp only [pow_one] at hshift htail
  simp only [Nat.sub_zero, pow_zero, div_one] at hpower
  unfold centeredDisplacementFirst
  apply (abs_sub _ _).trans
  apply add_le_add
  · apply (abs_sub _ _).trans
    apply add_le_add
    · rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hshift (Nat.cast_nonneg depth)
    · rw [abs_of_nonneg (by positivity)]
      calc
        _ ≤ ((depth + tailDepth : ℕ) : ℝ) * ratio ^ (depth + tailDepth - 1) :=
          mul_le_of_le_one_right (by positivity) haddress.2
        _ ≤ _ := mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
  · rw [abs_mul, abs_of_nonneg (pow_nonneg hpositive.le _)]
    exact mul_le_mul hpower hfirst (abs_nonneg _)
      (pow_nonneg (hpositive.le.trans hupper) depth)

theorem centeredDisplacement_second_uniform_bound
    {lower ratio upper firstBound secondBound : ℝ} (hlower : 0 < lower)
    (hratio : lower ≤ ratio) (hupper : ratio ≤ upper) (hless : upper < 1)
    (depth tailDepth : ℕ) (hdepth : 2 ≤ depth) (digits : ℕ → Bool)
    (hfirst : |deriv (fun parameter => address parameter digits) ratio| ≤ firstBound)
    (hsecond : |deriv (deriv (fun parameter => address parameter digits)) ratio| ≤ secondBound) :
    |centeredDisplacementSecond depth tailDepth digits ratio| ≤
      (depth : ℝ) * ((depth - 1 : ℕ) : ℝ) * (upper ^ depth / lower ^ 2) +
        ((depth + tailDepth : ℕ) : ℝ) * ((depth + tailDepth - 1 : ℕ) : ℝ) *
          (upper ^ depth / lower ^ 2) +
        2 * ((depth + tailDepth : ℕ) : ℝ) * (upper ^ depth / lower) * firstBound +
        upper ^ depth * secondBound := by
  have hpositive := hlower.trans_le hratio
  have hshift := centered_shifted_power_bound hlower hratio hupper depth 2 hdepth
  have htailSecond := centered_tail_shifted_power_bound hlower hratio hupper hless depth tailDepth 2 hdepth
  have htailFirst := centered_tail_shifted_power_bound hlower hratio hupper hless depth tailDepth 1 (by omega)
  have hpower := centered_tail_shifted_power_bound hlower hratio hupper hless depth tailDepth 0 (by omega)
  simp only [pow_one] at htailFirst
  simp only [Nat.sub_zero, pow_zero, div_one] at hpower
  have hfirstNonnegative : 0 ≤ firstBound := (abs_nonneg _).trans hfirst
  have hsecondNonnegative : 0 ≤ secondBound := (abs_nonneg _).trans hsecond
  apply (centeredDisplacement_second_bound depth tailDepth digits hpositive
    (hupper.trans_lt hless) hfirst hsecond).trans
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · simpa only [Nat.sub_sub] using mul_le_mul_of_nonneg_left hshift
          (show 0 ≤ (depth : ℝ) * ((depth - 1 : ℕ) : ℝ) by positivity)
      · simpa only [Nat.sub_sub] using mul_le_mul_of_nonneg_left htailSecond
          (show 0 ≤ ((depth + tailDepth : ℕ) : ℝ) *
            ((depth + tailDepth - 1 : ℕ) : ℝ) by positivity)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htailFirst (by positivity)) hfirstNonnegative
  · exact mul_le_mul_of_nonneg_right hpower hsecondNonnegative

/-- The first derivative has one polynomial depth factor while retaining
the pointwise exponential displacement scale. -/
theorem centeredDisplacement_first_polynomial_bound
    {lower ratio firstBound : ℝ} (hlower : 0 < lower)
    (hratio : lower ≤ ratio) (hless : ratio < 1)
    (depth tailDepth : ℕ) (hdepth : 1 ≤ depth) (htail : tailDepth ≤ depth)
    (digits : ℕ → Bool)
    (hfirst : |deriv (fun parameter => address parameter digits) ratio| ≤ firstBound) :
    |centeredDisplacementFirst depth tailDepth digits ratio| ≤
      (3 / lower + firstBound) * (depth : ℝ) * ratio ^ depth := by
  have hbound := centeredDisplacement_first_uniform_bound hlower hratio le_rfl hless
    depth tailDepth hdepth digits hfirst
  have hdepthReal : (1 : ℝ) ≤ depth := by exact_mod_cast hdepth
  have htailReal : (tailDepth : ℝ) ≤ depth := by exact_mod_cast htail
  have hfirstNonnegative : 0 ≤ firstBound := (abs_nonneg _).trans hfirst
  have htailTerm := mul_nonneg (sub_nonneg.mpr htailReal)
    (div_nonneg (pow_nonneg (hlower.le.trans hratio) depth) hlower.le)
  have hfirstTerm := mul_nonneg (sub_nonneg.mpr hdepthReal)
    (mul_nonneg (pow_nonneg (hlower.le.trans hratio) depth) hfirstNonnegative)
  apply hbound.trans
  simp only [Nat.cast_add, div_eq_mul_inv] at htailTerm ⊢
  nlinarith

theorem centeredDisplacement_second_polynomial_bound
    {lower ratio firstBound secondBound : ℝ} (hlower : 0 < lower)
    (hratio : lower ≤ ratio) (hless : ratio < 1)
    (depth tailDepth : ℕ) (hdepth : 2 ≤ depth) (htail : tailDepth ≤ depth)
    (digits : ℕ → Bool)
    (hfirst : |deriv (fun parameter => address parameter digits) ratio| ≤ firstBound)
    (hsecond : |deriv (deriv (fun parameter => address parameter digits)) ratio| ≤ secondBound) :
    |centeredDisplacementSecond depth tailDepth digits ratio| ≤
      (5 / lower ^ 2 + 4 * firstBound / lower + secondBound) *
        (depth : ℝ) ^ 2 * ratio ^ depth := by
  have hbound := centeredDisplacement_second_uniform_bound hlower hratio le_rfl hless
    depth tailDepth hdepth digits hfirst hsecond
  have hdepthReal : (2 : ℝ) ≤ depth := by exact_mod_cast hdepth
  have htailReal : (tailDepth : ℝ) ≤ depth := by exact_mod_cast htail
  have hpred : ((depth - 1 : ℕ) : ℝ) ≤ depth := by exact_mod_cast Nat.sub_le depth 1
  have htailPred : ((depth + tailDepth - 1 : ℕ) : ℝ) ≤ (depth + tailDepth : ℕ) := by
    exact_mod_cast Nat.sub_le (depth + tailDepth) 1
  have hfirstNonnegative : 0 ≤ firstBound := (abs_nonneg _).trans hfirst
  have hsecondNonnegative : 0 ≤ secondBound := (abs_nonneg _).trans hsecond
  have hfirstCoefficient : (depth : ℝ) * ((depth - 1 : ℕ) : ℝ) ≤ (depth : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hpred (Nat.cast_nonneg depth)]
  have htailDepth : ((depth + tailDepth : ℕ) : ℝ) ≤ 2 * depth := by
    simp only [Nat.cast_add]
    linarith
  have htailSquare := pow_le_pow_left₀ (Nat.cast_nonneg (depth + tailDepth)) htailDepth 2
  have hsecondCoefficient : ((depth + tailDepth : ℕ) : ℝ) *
      ((depth + tailDepth - 1 : ℕ) : ℝ) ≤ 4 * (depth : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left htailPred (Nat.cast_nonneg (depth + tailDepth))]
  have hthirdCoefficient : 2 * ((depth + tailDepth : ℕ) : ℝ) ≤ 4 * (depth : ℝ) ^ 2 := by
    nlinarith
  have hsquare : (1 : ℝ) ≤ (depth : ℝ) ^ 2 := by nlinarith
  have hfirstWeighted := mul_le_mul_of_nonneg_right hfirstCoefficient
    (div_nonneg (pow_nonneg (hlower.le.trans hratio) depth) (sq_nonneg lower))
  have hsecondWeighted := mul_le_mul_of_nonneg_right hsecondCoefficient
    (div_nonneg (pow_nonneg (hlower.le.trans hratio) depth) (sq_nonneg lower))
  have hthirdWeighted := mul_le_mul_of_nonneg_right hthirdCoefficient
    (mul_nonneg (div_nonneg (pow_nonneg (hlower.le.trans hratio) depth) hlower.le) hfirstNonnegative)
  have hfourthWeighted := mul_le_mul_of_nonneg_right hsquare
    (mul_nonneg (pow_nonneg (hlower.le.trans hratio) depth) hsecondNonnegative)
  apply hbound.trans
  simp only [div_eq_mul_inv] at hfirstWeighted hsecondWeighted hthirdWeighted ⊢
  nlinarith

end LambdaCantor.AE
