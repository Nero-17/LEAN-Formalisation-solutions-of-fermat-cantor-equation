import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace LambdaCantor.AE

/-- Exact factorisation of the polynomial in (4.1). -/
theorem transversality_polynomial_factor (ratio : ℝ) :
    2 * ratio ^ 3 - 3 * ratio ^ 2 + 3 * ratio - 1 =
      (2 * ratio - 1) * (ratio ^ 2 - ratio + 1) := by ring

theorem transversality_polynomial_neg {ratio : ℝ}
    (hhalf : ratio < 1 / 2) :
    2 * ratio ^ 3 - 3 * ratio ^ 2 + 3 * ratio - 1 < 0 := by
  rw [transversality_polynomial_factor]
  apply mul_neg_of_neg_of_pos
  · linarith
  · nlinarith [sq_nonneg (ratio - 1 / 2)]

/-- The strict numerical transversality bound used in Lemma 4.1. -/
theorem transversality_bound_neg {ratio : ℝ}
    (hpos : 0 < ratio) (hhalf : ratio < 1 / 2) :
    -(2 / ratio) + 2 + 2 * ratio ^ 2 / (1 - ratio) ^ 2 < 0 := by
  have hleft : 0 < 1 - ratio := by linarith
  have hdenom : 0 < ratio * (1 - ratio) ^ 2 := by positivity
  have hidentity :
      (-(2 / ratio) + 2 + 2 * ratio ^ 2 / (1 - ratio) ^ 2) *
        (ratio * (1 - ratio) ^ 2) =
        2 * (2 * ratio ^ 3 - 3 * ratio ^ 2 + 3 * ratio - 1) := by
    field_simp [hpos.ne', hleft.ne']
    <;> ring
  have hpoly := transversality_polynomial_neg hhalf
  by_contra hnotnegative
  have hnonnegative := mul_nonneg (le_of_not_gt hnotnegative) hdenom.le
  nlinarith

/-- The numerical upper bound is increasing on the positive half interval,
so its value at the right endpoint gives a uniform negative margin. -/
theorem transversality_bound_mono {ratio upper : ℝ}
    (hpos : 0 < ratio) (hle : ratio ≤ upper) (hupper : upper < 1 / 2) :
    -(2 / ratio) + 2 + 2 * ratio ^ 2 / (1 - ratio) ^ 2 ≤
      -(2 / upper) + 2 + 2 * upper ^ 2 / (1 - upper) ^ 2 := by
  have hupperpos := hpos.trans_le hle
  have hratioone : 0 < 1 - ratio := by linarith
  have hupperone : 0 < 1 - upper := by linarith
  have hinverse : 2 / upper ≤ 2 / ratio := by
    apply (div_le_div_iff₀ hupperpos hpos).mpr
    linarith
  have hquotient : ratio / (1 - ratio) ≤ upper / (1 - upper) := by
    apply (div_le_div_iff₀ hratioone hupperone).mpr
    nlinarith
  have hsquare := mul_self_le_mul_self (div_nonneg hpos.le hratioone.le) hquotient
  have hnormalize (point : ℝ) :
      2 * point ^ 2 / (1 - point) ^ 2 = 2 * (point / (1 - point)) ^ 2 := by
    rw [div_pow]
    ring
  rw [hnormalize ratio, hnormalize upper]
  nlinarith

/-- A uniform strictly negative derivative follows from the differential
inequality and a sufficiently small value of the function. -/
theorem derivative_neg_of_small_value {value derivative ratio margin : ℝ}
    (hpos : 0 < ratio) (hmargin : 0 < margin)
    (hbound : derivative - (2 / ratio) * value ≤ -margin)
    (hsmall : |value| < margin * ratio / 4) :
    derivative < -(margin / 2) := by
  have hupper : value < margin * ratio / 4 := (abs_lt.mp hsmall).2
  have hproduct : (2 / ratio) * value < margin / 2 := by
    calc
      (2 / ratio) * value = (2 * value) / ratio := by ring
      _ < margin / 2 := (div_lt_iff₀ hpos).mpr (by nlinarith)
  linarith

/-- Agreement probability for two independent self-convolution digits. -/
theorem digit_agreement_probability :
    (1 / 4 : ℝ) ^ 2 + (1 / 2) ^ 2 + (1 / 4) ^ 2 = 3 / 8 := by norm_num

end LambdaCantor.AE
