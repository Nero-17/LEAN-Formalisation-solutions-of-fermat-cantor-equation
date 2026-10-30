import LambdaCantor.AE.DigitResidual

namespace LambdaCantor.AE

/-- A uniform second-derivative bound for the actual first-difference
prefactor. The constant depends only on the lower endpoint. -/
theorem firstDifferencePrefactor_secondDerivative_bound (depth : ℕ)
    {lower ratio : ℝ} (hlower : 0 < lower) (horder : lower ≤ ratio) (hlt : ratio < 1) :
    |deriv (deriv (firstDifferencePrefactor depth)) ratio| ≤
      (2 / lower + 1 / lower ^ 2) * ((depth + 1 : ℕ) : ℝ) ^ 2 * ratio ^ depth := by
  have hpos := hlower.trans_le horder
  have hfirstnonneg : 0 ≤ (depth : ℝ) * ratio ^ (depth - 1) := by positivity
  have hsecondnonneg : 0 ≤ (depth : ℝ) * (depth - 1 : ℕ) * ratio ^ (depth - 2) := by positivity
  have hfirstidentity : ratio * ((depth : ℝ) * ratio ^ (depth - 1)) =
      (depth : ℝ) * ratio ^ depth := by
    cases depth with
    | zero => simp
    | succ depth => simp only [Nat.succ_sub_one, pow_succ]; ring
  have hsecondidentity : ratio ^ 2 *
      ((depth : ℝ) * (depth - 1 : ℕ) * ratio ^ (depth - 2)) =
      (depth : ℝ) * (depth - 1 : ℕ) * ratio ^ depth := by
    cases depth with
    | zero => simp
    | succ depth =>
      cases depth with
      | zero => simp
      | succ depth =>
        rw [show Nat.succ (Nat.succ depth) - 2 = depth by omega]
        simp only [pow_succ]
        ring
  have hfirst : (depth : ℝ) * ratio ^ (depth - 1) ≤
      (depth : ℝ) / lower * ratio ^ depth := by
    have hmul := mul_le_mul_of_nonneg_right horder hfirstnonneg
    rw [hfirstidentity] at hmul
    calc
      _ ≤ ((depth : ℝ) * ratio ^ depth) / lower :=
        (le_div_iff₀ hlower).mpr (by simpa only [mul_comm] using hmul)
      _ = _ := by ring
  have hsecond : (depth : ℝ) * (depth - 1 : ℕ) * ratio ^ (depth - 2) ≤
      ((depth : ℝ) * (depth - 1 : ℕ)) / lower ^ 2 * ratio ^ depth := by
    have hsquare : lower ^ 2 ≤ ratio ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hsquare hsecondnonneg
    rw [hsecondidentity] at hmul
    calc
      _ ≤ ((depth : ℝ) * (depth - 1 : ℕ) * ratio ^ depth) / lower ^ 2 :=
        (le_div_iff₀ (sq_pos_of_pos hlower)).mpr (by simpa only [mul_comm] using hmul)
      _ = _ := by ring
  have hdepth : (0 : ℝ) ≤ depth := Nat.cast_nonneg _
  have hpred : ((depth - 1 : ℕ) : ℝ) ≤ depth := by exact_mod_cast Nat.sub_le depth 1
  have hpolyfirst : (depth : ℝ) ≤ ((depth + 1 : ℕ) : ℝ) ^ 2 := by push_cast; nlinarith
  have hpolysecond : (depth : ℝ) * (depth - 1 : ℕ) ≤ ((depth + 1 : ℕ) : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hpred hdepth
    push_cast
    nlinarith
  have hcoefficient : 2 * ((depth : ℝ) / lower) +
      ((depth : ℝ) * (depth - 1 : ℕ)) / lower ^ 2 ≤
        (2 / lower + 1 / lower ^ 2) * ((depth + 1 : ℕ) : ℝ) ^ 2 := by
    have hfirstmul := mul_le_mul_of_nonneg_left hpolyfirst (show 0 ≤ 2 / lower by positivity)
    have hsecondmul := mul_le_mul_of_nonneg_left hpolysecond (show 0 ≤ 1 / lower ^ 2 by positivity)
    calc
      _ = (2/lower)*(depth : ℝ) + (1/lower^2)*((depth : ℝ)*(depth-1 : ℕ)) := by ring
      _ ≤ (2/lower)*((depth+1 : ℕ) : ℝ)^2 +
          (1/lower^2)*((depth+1 : ℕ) : ℝ)^2 := add_le_add hfirstmul hsecondmul
      _ = _ := by ring
  rw [(hasDerivAt_deriv_firstDifferencePrefactor depth ratio).deriv]
  calc
    _ ≤ |-2 * (depth : ℝ) * ratio ^ (depth - 1)| +
        |(1 - ratio) * (depth : ℝ) * (depth - 1 : ℕ) * ratio ^ (depth - 2)| := abs_add_le _ _
    _ = 2 * ((depth : ℝ) * ratio ^ (depth - 1)) +
        (1 - ratio) * ((depth : ℝ) * (depth - 1 : ℕ) * ratio ^ (depth - 2)) := by
      rw [abs_of_nonpos (by nlinarith), abs_of_nonneg (by positivity)]
      ring
    _ ≤ (2 * ((depth : ℝ) / lower) +
        ((depth : ℝ) * (depth - 1 : ℕ)) / lower ^ 2) * ratio ^ depth := by
      have hgap := mul_le_mul_of_nonneg_right (show 1 - ratio ≤ 1 by linarith) hsecondnonneg
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoefficient (pow_nonneg hpos.le depth)

end LambdaCantor.AE
