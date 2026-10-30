import LambdaCantor.First.RpowTaylor
import LambdaCantor.First.RpowQuotient
import Mathlib.Tactic.FieldSimp

namespace LambdaCantor

/-- Exact normalization of the two-cylinder residual for a real exponent.
The phase is the actual difference between the integer depths. -/
theorem normalized_real_residual_identity {ratio exponent amplitude tail : ℝ}
    (hratio : 0 < ratio) (hamplitude : 0 ≤ amplitude) (leftDepth rightDepth : ℕ) :
    ((ratio ^ leftDepth * amplitude) ^ exponent +
        (1 - ratio ^ rightDepth * tail) ^ exponent - 1) /
        ratio ^ (exponent * (leftDepth : ℝ)) -
      (amplitude ^ exponent - exponent *
        ratio ^ ((rightDepth : ℝ) - exponent * (leftDepth : ℝ)) * tail) =
      ((1 - ratio ^ rightDepth * tail) ^ exponent - 1 +
        exponent * (ratio ^ rightDepth * tail)) /
        ratio ^ (exponent * (leftDepth : ℝ)) := by
  have hpower : (ratio ^ leftDepth) ^ exponent = ratio ^ (exponent * (leftDepth : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hratio.le, mul_comm]
  rw [Real.mul_rpow (pow_nonneg hratio.le leftDepth) hamplitude, hpower,
    Real.rpow_sub hratio, Real.rpow_natCast]
  have hne : ratio ^ (exponent * (leftDepth : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos hratio _).ne'
  field_simp [hne]
  <;> ring

/-- Uniform quadratic control of the exact normalized error. All quantities
are the genuine power residual, rather than an assumed approximation. -/
theorem normalized_real_residual_bound (exponent : ℝ) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (ratio amplitude tail : ℝ) (leftDepth rightDepth : ℕ),
        0 < ratio → 0 ≤ amplitude →
        ratio ^ rightDepth * tail ∈ Set.Icc (0 : ℝ) (1 / 2) →
      |((ratio ^ leftDepth * amplitude) ^ exponent +
          (1 - ratio ^ rightDepth * tail) ^ exponent - 1) /
          ratio ^ (exponent * (leftDepth : ℝ)) -
        (amplitude ^ exponent - exponent *
          ratio ^ ((rightDepth : ℝ) - exponent * (leftDepth : ℝ)) * tail)| ≤
        constant * (ratio ^ rightDepth * tail) ^ 2 /
          ratio ^ (exponent * (leftDepth : ℝ)) := by
  obtain ⟨constant, hpositive, hbound⟩ := exists_rpow_quadratic_remainder_bound exponent
  refine ⟨constant, hpositive, ?_⟩
  intro ratio amplitude tail leftDepth rightDepth hratio hamplitude htail
  rw [normalized_real_residual_identity hratio hamplitude, abs_div,
    abs_of_pos (Real.rpow_pos_of_pos hratio _)]
  exact div_le_div_of_nonneg_right (hbound _ htail) (Real.rpow_pos_of_pos hratio _).le

/-- Factoring the normalized error through the divided remainder avoids
differentiating a large inverse power in the uniform C1 estimate. -/
theorem normalized_real_residual_quotient {ratio exponent amplitude tail : ℝ}
    (hratio : 0 < ratio) (hamplitude : 0 ≤ amplitude) (htail : 0 < tail)
    (leftDepth rightDepth : ℕ) :
    ((ratio ^ leftDepth * amplitude) ^ exponent +
        (1 - ratio ^ rightDepth * tail) ^ exponent - 1) /
        ratio ^ (exponent * (leftDepth : ℝ)) -
      (amplitude ^ exponent - exponent *
        ratio ^ ((rightDepth : ℝ) - exponent * (leftDepth : ℝ)) * tail) =
      ratio ^ ((rightDepth : ℝ) - exponent * (leftDepth : ℝ)) * tail *
        rpowRemainderQuotient exponent (ratio ^ rightDepth * tail) := by
  rw [normalized_real_residual_identity hratio hamplitude,
    Real.rpow_sub hratio, Real.rpow_natCast]
  unfold rpowRemainderQuotient
  have hdenominator : ratio ^ (exponent * (leftDepth : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos hratio _).ne'
  have hscale : ratio ^ rightDepth * tail ≠ 0 :=
    (mul_pos (pow_pos hratio _) htail).ne'
  field_simp [hdenominator, hscale]
  <;> ring

end LambdaCantor
