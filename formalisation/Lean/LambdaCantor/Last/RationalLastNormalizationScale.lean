import LambdaCantor.Last.ArithmeticField
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor.Last

/-- Independent nonnegative prefix depths normalize every positive gradient
ratio into the half-open fundamental interval. Both depths are constructed
from actual powers of the contraction. -/
theorem exists_natural_prefix_slope_normalization {ratio slope : ℝ}
    (ratio_positive : 0 < ratio) (ratio_less_one : ratio < 1) (slope_positive : 0 < slope) :
    ∃ firstDepth secondDepth : ℕ,
      1 ≤ ratio^secondDepth/ratio^firstDepth*slope ∧
        ratio^secondDepth/ratio^firstDepth*slope < 1/ratio := by
  classical
  obtain ⟨secondDepth, contracted⟩ := exists_pow_lt_of_lt_one
    (div_pos zero_lt_one slope_positive) ratio_less_one
  have contracted_positive : 0 < ratio^secondDepth*slope := mul_pos (pow_pos ratio_positive _) slope_positive
  have contracted_small : ratio^secondDepth*slope < 1 :=
    (lt_div_iff₀ slope_positive).mp contracted
  have exists_first : ∃ firstDepth : ℕ, ratio^firstDepth ≤ ratio^secondDepth*slope := by
    obtain ⟨firstDepth, small⟩ := exists_pow_lt_of_lt_one contracted_positive ratio_less_one
    exact ⟨firstDepth, small.le⟩
  let firstDepth := Nat.find exists_first
  have first_bound : ratio^firstDepth ≤ ratio^secondDepth*slope := Nat.find_spec exists_first
  have first_positive : 0 < firstDepth := by
    by_contra failure
    have zero : firstDepth = 0 := by omega
    rw [zero, pow_zero] at first_bound
    linarith
  have previous_bound : ratio^secondDepth*slope < ratio^(firstDepth-1) :=
    lt_of_not_ge (Nat.find_min exists_first (show firstDepth-1 < Nat.find exists_first by
      change firstDepth-1 < firstDepth
      omega))
  have power_identity : ratio^firstDepth = ratio^(firstDepth-1)*ratio := by
    rw [← pow_succ]
    congr 1
    omega
  refine ⟨firstDepth, secondDepth, ?_, ?_⟩
  · have lower : 1 ≤ (ratio^secondDepth*slope)/ratio^firstDepth :=
      (one_le_div (pow_pos ratio_positive _)).mpr first_bound
    convert lower using 1 <;> ring
  · apply (lt_div_iff₀ ratio_positive).mpr
    have upper : (ratio^secondDepth*slope)/ratio^(firstDepth-1) < 1 :=
      (div_lt_one (pow_pos ratio_positive _)).mpr previous_bound
    calc
      ratio^secondDepth/ratio^firstDepth*slope*ratio =
          (ratio^secondDepth*slope)/ratio^(firstDepth-1) := by
        rw [power_identity]
        field_simp [ratio_positive.ne', (pow_pos ratio_positive (firstDepth-1)).ne']
        <;> ring
      _ < 1 := upper

theorem normalized_prefix_slope_not_mem_parameterField {ratio slope : ℝ}
    (ratio_positive : 0 < ratio) (outside : slope ∉ parameterField ratio)
    (firstDepth secondDepth : ℕ) :
    ratio^secondDepth/ratio^firstDepth*slope ∉ parameterField ratio := by
  apply mul_not_mem_parameterField
  · exact (parameterField ratio).div_mem
      ((parameterField ratio).pow_mem (ratio_mem_parameterField ratio) secondDepth)
      ((parameterField ratio).pow_mem (ratio_mem_parameterField ratio) firstDepth)
  · exact div_ne_zero (pow_ne_zero _ ratio_positive.ne') (pow_ne_zero _ ratio_positive.ne')
  · exact outside

end LambdaCantor.Last
