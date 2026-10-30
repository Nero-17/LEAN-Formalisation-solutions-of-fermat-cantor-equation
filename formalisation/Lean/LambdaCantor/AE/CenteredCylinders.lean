import LambdaCantor.Last.ReturnWords

noncomputable section
namespace LambdaCantor.AE
open LambdaCantor.Last

def centeredCylinder (ratio : ℝ) (horizontalDepth verticalDepth tailDepth : ℕ)
    (point : ℝ × ℝ) : ℝ × ℝ :=
  (ratio ^ horizontalDepth * (1 - ratio ^ tailDepth + ratio ^ tailDepth * point.1),
    1 - ratio ^ verticalDepth + ratio ^ (verticalDepth + tailDepth) * point.2)

theorem lower_corner_word (ratio : ℝ) (depth : ℕ) (point : ℝ × ℝ) :
    wordMap ratio (List.replicate depth (false, false)) point = ratio ^ depth • point := by
  induction depth with
  | zero => simp [wordMap]
  | succ depth ih =>
    simp only [List.replicate_succ, wordMap, digitPoint, Bool.false_eq_true, if_false,
      ih, pow_succ]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] <;> ring

theorem upper_corner_word (ratio : ℝ) (depth : ℕ) (point : ℝ × ℝ) :
    wordMap ratio (List.replicate depth (true, true)) point =
      (1 - ratio ^ depth, 1 - ratio ^ depth) + ratio ^ depth • point := by
  induction depth with
  | zero => ext <;> simp [wordMap]
  | succ depth ih =>
    simp only [List.replicate_succ, wordMap, digitPoint, if_true, ih, pow_succ]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] <;> ring

theorem centeredCylinder_mem_dust {ratio : ℝ} (hnonnegative : 0 ≤ ratio) (hless : ratio < 1)
    (horizontalDepth verticalDepth tailDepth : ℕ) {point : ℝ × ℝ}
    (hpoint : point ∈ cantorDust ratio) :
    centeredCylinder ratio horizontalDepth verticalDepth tailDepth point ∈ cantorDust ratio := by
  have hlower := wordMap_mem_dust hnonnegative hless
    (List.replicate horizontalDepth (false, false))
    (wordMap_mem_dust hnonnegative hless (List.replicate tailDepth (true, true)) hpoint)
  have hupper := wordMap_mem_dust hnonnegative hless
    (List.replicate verticalDepth (true, true))
    (wordMap_mem_dust hnonnegative hless (List.replicate tailDepth (false, false)) hpoint)
  rw [lower_corner_word, upper_corner_word] at hlower
  rw [upper_corner_word, lower_corner_word] at hupper
  constructor
  · simpa only [centeredCylinder, Prod.smul_fst, Prod.fst_add, smul_eq_mul] using hlower.1
  · simpa only [centeredCylinder, Prod.snd_add, Prod.smul_snd, smul_eq_mul,
      pow_add, mul_assoc] using hupper.2

def centeredTaylorRemainder (exponent displacement : ℝ) : ℝ :=
  (1 - displacement) ^ exponent - 1 + exponent * displacement

theorem centered_displacement_bounds {ratio : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1)
    (verticalDepth tailDepth : ℕ) {tail : ℝ} (htail : tail ∈ Set.Icc (0 : ℝ) 1) :
    ratio ^ verticalDepth * (1 - ratio ^ tailDepth) ≤
      ratio ^ verticalDepth * (1 - ratio ^ tailDepth * tail) ∧
    ratio ^ verticalDepth * (1 - ratio ^ tailDepth * tail) ≤ ratio ^ verticalDepth := by
  have hnonnegative := pow_nonneg hpositive.le tailDepth
  constructor
  · apply mul_le_mul_of_nonneg_left _ (pow_nonneg hpositive.le verticalDepth)
    nlinarith [mul_le_mul_of_nonneg_left htail.2 hnonnegative]
  · have hproduct := mul_nonneg hnonnegative htail.1
    nlinarith [mul_nonneg (pow_nonneg hpositive.le verticalDepth) hproduct]

theorem centeredTaylorRemainder_zero (exponent : ℝ) :
    centeredTaylorRemainder exponent 0 = 0 := by
  simp [centeredTaylorRemainder]

/-- Exact decomposition underlying the paper's centered-residual expansion.
The remainder is explicit; this theorem makes no unproved asymptotic assertion. -/
theorem centeredCylinder_residual (exponent ratio : ℝ) (hpositive : 0 < ratio)
    (hless : ratio < 1) (horizontalDepth verticalDepth tailDepth : ℕ)
    (point : ℝ × ℝ) (hfirst : 0 ≤ point.1) :
    (((centeredCylinder ratio horizontalDepth verticalDepth tailDepth point).1 ^ exponent +
      (centeredCylinder ratio horizontalDepth verticalDepth tailDepth point).2 ^ exponent - 1) /
      ratio ^ (exponent * horizontalDepth)) =
    (1 - ratio ^ tailDepth + ratio ^ tailDepth * point.1) ^ exponent -
      exponent * ratio ^ ((verticalDepth : ℝ) - exponent * horizontalDepth) *
        (1 - ratio ^ tailDepth * point.2) +
      centeredTaylorRemainder exponent (ratio ^ verticalDepth * (1 - ratio ^ tailDepth * point.2)) /
        ratio ^ (exponent * horizontalDepth) := by
  have hhorizontal :
      (ratio ^ horizontalDepth * (1 - ratio ^ tailDepth + ratio ^ tailDepth * point.1)) ^ exponent =
      ratio ^ (exponent * horizontalDepth) *
        (1 - ratio ^ tailDepth + ratio ^ tailDepth * point.1) ^ exponent := by
    rw [Real.mul_rpow (pow_nonneg hpositive.le _) ?_]
    · rw [← Real.rpow_natCast_mul hpositive.le]
      congr 2
      ring
    · have hpower := pow_le_one₀ hpositive.le hless.le (n := tailDepth)
      nlinarith [mul_nonneg (pow_nonneg hpositive.le tailDepth) hfirst]
  have hvertical : 1 - ratio ^ verticalDepth + ratio ^ (verticalDepth + tailDepth) * point.2 =
      1 - ratio ^ verticalDepth * (1 - ratio ^ tailDepth * point.2) := by
    rw [pow_add]
    ring
  have hscale : ratio ^ (exponent * horizontalDepth) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hpositive _)
  have hquotient : ratio ^ ((verticalDepth : ℝ) - exponent * horizontalDepth) =
      ratio ^ verticalDepth / ratio ^ (exponent * horizontalDepth) := by
    rw [Real.rpow_sub hpositive, Real.rpow_natCast]
  simp only [centeredCylinder]
  rw [hhorizontal, hvertical, hquotient]
  unfold centeredTaylorRemainder
  field_simp [hscale]
  <;> ring

end LambdaCantor.AE
