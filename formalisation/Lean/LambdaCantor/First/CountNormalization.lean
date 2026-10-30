import LambdaCantor.First.GraphBranching
import LambdaCantor.First.BlockSelection

noncomputable section
namespace LambdaCantor.First.PrefixSlopes

open Set MeasureTheory
open scoped ENNReal NNReal

theorem count_le_of_weighted_strip_bound {ratio slope constant exponent : ℝ}
    (hratio : 0 ≤ ratio) (hconstant : 0 ≤ constant) {count block : ℕ}
    (hbound : (count : ℝ≥0∞) * (1 / 4 : ℝ≥0∞) ^ block ≤
      ENNReal.ofReal (constant * ((|slope| + 3) * ratio ^ block) ^ exponent)) :
    (count : ℝ) ≤ constant * (|slope| + 3) ^ exponent * (4 * ratio ^ exponent) ^ block := by
  have hnonnegative : 0 ≤ constant * ((|slope| + 3) * ratio ^ block) ^ exponent :=
    mul_nonneg hconstant (Real.rpow_nonneg (by positivity) _)
  have hreal : (count : ℝ) * (1 / 4 : ℝ) ^ block ≤
      constant * ((|slope| + 3) * ratio ^ block) ^ exponent := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal hnonnegative] using
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound)
  calc
    (count : ℝ) = ((count : ℝ) * (1 / 4 : ℝ) ^ block) * 4 ^ block := by
      rw [mul_assoc, ← mul_pow]
      norm_num
    _ ≤ (constant * ((|slope| + 3) * ratio ^ block) ^ exponent) * 4 ^ block :=
      mul_le_mul_of_nonneg_right hreal (pow_nonneg (by norm_num) block)
    _ = constant * (|slope| + 3) ^ exponent * (4 * ratio ^ exponent) ^ block := by
      rw [Real.mul_rpow (by positivity) (pow_nonneg hratio block),
        ← Real.rpow_pow_comm hratio, mul_pow]
      ring

theorem active_child_card_le_ceiling {ratio slope constant exponent : ℝ}
    (hratio : 0 < ratio) (hcontract : ratio < 1) (hconstant : 0 ≤ constant)
    (hball : ∀ center radius : ℝ, 0 < radius →
      projectedMeasure ratio slope (Metric.ball center radius) ≤
        ENNReal.ofReal (constant * radius ^ exponent))
    {target : Set (ℝ × ℝ)} {prefixLength block : ℕ}
    (hflat : ∀ left ∈ target, ∀ right ∈ target,
      |(left.2 - right.2) - slope * (left.1 - right.1)| ≤
        ratio ^ block * |left.1 - right.1|)
    (parent : Fin prefixLength → Bool × Bool)
    (hparent : parent ∈ activeWords ratio target prefixLength) :
    ((activeWords ratio target (prefixLength + block)).filter
      (fun word => wordParent word = parent)).card ≤
      Nat.ceil (constant * (|slope| + 3) ^ exponent * (4 * ratio ^ exponent) ^ block) := by
  classical
  have hreal := (count_le_of_weighted_strip_bound hratio.le hconstant
    (active_child_strip_count hratio hcontract hball hflat parent hparent)).trans (Nat.le_ceil _)
  exact_mod_cast hreal

end LambdaCantor.First.PrefixSlopes
