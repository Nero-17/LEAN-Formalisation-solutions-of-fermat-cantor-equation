import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace LambdaCantor.AE

theorem inverse_square_le_firstDifference_scale (depth : ℕ)
    {lower upper : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper) :
    1 / (lower ^ depth) ^ 2 ≤ (upper / lower ^ 3) ^ depth := by
  have hpowerIdentity : (upper / lower ^ 3) ^ depth = upper ^ depth / (lower ^ depth) ^ 3 := by
    rw [div_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 3 depth]
  rw [hpowerIdentity]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hmul := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlower.le horder depth)
    (sq_nonneg (lower ^ depth))
  nlinarith

/-- The three terms of the actual inverse-density derivative estimate have
the same summable first-difference scale. This is the arithmetic used in
the near-band parameter-kernel estimate. -/
theorem inverseDensity_firstDifference_scale (depth : ℕ)
    {lower upper epsilon margin parameterBound parameterDerivativeBound cutoffBound secondBound : ℝ}
    (hlower : 0 < lower) (horder : lower ≤ upper) (hepsilon : 0 < epsilon) (hmargin : 0 < margin)
    (hparameter : 0 ≤ parameterBound) (hparameterDerivative : 0 ≤ parameterDerivativeBound)
    (hcutoff : 0 ≤ cutoffBound) (hsecond : 0 ≤ secondBound) :
    parameterDerivativeBound / (margin * lower ^ depth) ^ 2 +
      parameterBound * (cutoffBound / (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ))) /
        (margin * lower ^ depth) +
      parameterBound * (secondBound * ((depth + 1 : ℕ) : ℝ) ^ 2 * upper ^ depth) /
        (margin * lower ^ depth) ^ 3 ≤
    (parameterDerivativeBound / margin ^ 2 + parameterBound * cutoffBound / (epsilon * margin) +
      parameterBound * secondBound / margin ^ 3) *
        ((depth + 1 : ℕ) : ℝ) ^ 2 * (upper / lower ^ 3) ^ depth := by
  have hlowerPower : 0 < lower ^ depth := pow_pos hlower depth
  have hupper := hlower.trans_le horder
  have hdepth : 0 < ((depth + 1 : ℕ) : ℝ) := by positivity
  have hdepthone : (1 : ℝ) ≤ ((depth + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le depth)
  have hdepthsquare : ((depth + 1 : ℕ) : ℝ) ≤ ((depth + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hdepthsquareone : (1 : ℝ) ≤ ((depth + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hpowerIdentity : (upper / lower ^ 3) ^ depth = upper ^ depth / (lower ^ depth) ^ 3 := by
    rw [div_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 3 depth]
  have hbase : 1 / (lower ^ depth) ^ 2 ≤ (upper / lower ^ 3) ^ depth := by
    rw [hpowerIdentity]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hmul := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlower.le horder depth)
      (sq_nonneg (lower ^ depth))
    nlinarith
  have hfirst := mul_le_mul_of_nonneg_left hbase
    (show 0 ≤ parameterDerivativeBound / margin ^ 2 by positivity)
  have hfirstGrowth := mul_le_mul_of_nonneg_left hdepthsquareone
    (show 0 ≤ parameterDerivativeBound / margin ^ 2 * (upper / lower ^ 3) ^ depth by positivity)
  have hmiddle := mul_le_mul_of_nonneg_left hbase
    (show 0 ≤ parameterBound * cutoffBound / (epsilon * margin) * ((depth + 1 : ℕ) : ℝ) by positivity)
  have hmiddleGrowth := mul_le_mul_of_nonneg_left hdepthsquare
    (show 0 ≤ parameterBound * cutoffBound / (epsilon * margin) * (upper / lower ^ 3) ^ depth by positivity)
  have hdecomposition :
      parameterDerivativeBound / (margin * lower ^ depth) ^ 2 +
        parameterBound * (cutoffBound / (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ))) /
          (margin * lower ^ depth) +
        parameterBound * (secondBound * ((depth + 1 : ℕ) : ℝ) ^ 2 * upper ^ depth) /
          (margin * lower ^ depth) ^ 3 =
      (parameterDerivativeBound / margin ^ 2) * (1 / (lower ^ depth) ^ 2) +
        (parameterBound * cutoffBound / (epsilon * margin) * ((depth + 1 : ℕ) : ℝ)) *
          (1 / (lower ^ depth) ^ 2) +
        (parameterBound * secondBound / margin ^ 3) * ((depth + 1 : ℕ) : ℝ) ^ 2 *
          (upper / lower ^ 3) ^ depth := by
    rw [hpowerIdentity]
    field_simp [ne_of_gt hlowerPower, ne_of_gt hepsilon, ne_of_gt hmargin, ne_of_gt hdepth]
    <;> ring
  rw [hdecomposition]
  nlinarith

end LambdaCantor.AE
