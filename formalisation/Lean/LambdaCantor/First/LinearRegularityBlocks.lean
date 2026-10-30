import LambdaCantor.First.LinearRegularityDigits
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.FunProp

noncomputable section
open scoped BigOperators
namespace LambdaCantor.First.LinearRegularity

/-- The retained paired digits in one length-M block. Residue zero is sparse,
so exactly M-1 paired positions remain. -/
abbrev DenseBlock (blockLength : ℕ) := Fin (blockLength - 1) → Bool × Bool

/-- Exact number of equal-weight dense block symbols. -/
theorem denseBlock_card (blockLength : ℕ) :
    Fintype.card (DenseBlock blockLength) = 4 ^ (blockLength - 1) := by
  simp [DenseBlock, Fintype.card_fun, Fintype.card_prod]

/-- Actual affine translation produced by the retained positions of a paired
block, with the same normalization as the full Cantor address. -/
def denseBlockTranslation (blockLength : ℕ) (parameter : ℝ × ℝ)
    (word : DenseBlock blockLength) : ℝ :=
  (1 - parameter.1) * ∑ offset : Fin (blockLength - 1),
    (parameter.2 * (if (word offset).1 then (1 : ℝ) else 0) +
      (if (word offset).2 then (1 : ℝ) else 0)) * parameter.1 ^ ((offset : ℕ) + 1)

/-- The dense block contraction is analytic on the full parameter plane. -/
theorem denseBlockContraction_analytic (blockLength : ℕ) (domain : Set (ℝ × ℝ)) :
    AnalyticOnNhd ℝ (fun parameter : ℝ × ℝ => parameter.1 ^ blockLength) domain := by
  intro parameter hparameter
  exact analyticAt_fst.pow blockLength

/-- Every actual dense block translation is an analytic polynomial in
contraction and slope. -/
theorem denseBlockTranslation_analytic (blockLength : ℕ) (word : DenseBlock blockLength)
    (domain : Set (ℝ × ℝ)) :
    AnalyticOnNhd ℝ (fun parameter => denseBlockTranslation blockLength parameter word) domain := by
  intro parameter hparameter
  unfold denseBlockTranslation
  apply AnalyticAt.mul
  · exact analyticAt_const.sub analyticAt_fst
  · apply Finset.analyticAt_fun_sum
    intro offset hoffset
    exact ((analyticAt_snd.mul analyticAt_const).add analyticAt_const).mul
      (analyticAt_fst.pow ((offset : ℕ) + 1))

/-- Block contractions remain strictly between zero and one. -/
theorem denseBlockContraction_mem_unit {ratio : ℝ} (hratio : 0 < ratio) (hcontract : ratio < 1)
    (blockLength : ℕ) (hblockLength : 0 < blockLength) :
    0 < ratio ^ blockLength ∧ ratio ^ blockLength < 1 := by
  exact ⟨pow_pos hratio _, pow_lt_one₀ hratio.le hcontract (Nat.ne_of_gt hblockLength)⟩

end LambdaCantor.First.LinearRegularity
