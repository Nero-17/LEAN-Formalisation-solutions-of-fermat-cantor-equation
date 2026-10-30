import LambdaCantor.First.PrefixSlopes

/-! The actual projected Cantor words satisfy exponential separation off
the zero-dimensional collision set constructed in `PrefixSlopes`. -/

noncomputable section
namespace LambdaCantor.First.PrefixSlopes

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

def digitEquiv : Fin 4 ≃ Bool × Bool :=
  (Fintype.equivFinOfCardEq (by decide : Fintype.card (Bool × Bool) = 4)).symm

def projectedDigit (ratio slope : ℝ) (digit : Fin 4) : ℝ :=
  (1 - ratio) * (if (digitEquiv digit).2 then 1 else 0) -
    slope * ((1 - ratio) * (if (digitEquiv digit).1 then 1 else 0))

theorem finiteAddress_eq_sum (ratio : ℝ) {depth : ℕ} (word : Fin depth → Bool) :
    finiteAddress ratio word =
      ∑ position : Fin depth,
        ratio ^ (position : ℕ) * ((1 - ratio) * (if word position then 1 else 0)) := by
  unfold finiteAddress address
  rw [tsum_eq_sum (s := Finset.range depth)]
  · rw [← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro position _
    simp only [extendWord, dif_pos position.isLt]
    ring
  · intro position houtside
    have hposition : ¬ position < depth := by simpa using houtside
    simp [extendWord, hposition]

def wordIndex {depth : ℕ} (word : Fin depth → Fin 4) : Fin (4 ^ depth) :=
  planarWordEquiv depth (fun position => digitEquiv (word position))

theorem wordIndex_injective (depth : ℕ) : Function.Injective (wordIndex (depth := depth)) := by
  intro left right hequal
  have h := (planarWordEquiv depth).injective hequal
  funext position
  exact digitEquiv.injective (congrFun h position)

theorem projected_word_eq (ratio slope : ℝ) {depth : ℕ} (word : Fin depth → Fin 4) :
    ExternalProjection.wordTranslation ratio (projectedDigit ratio slope) word =
      (planarTranslation ratio depth (wordIndex word)).2 -
        slope * (planarTranslation ratio depth (wordIndex word)).1 := by
  simp only [planarTranslation, wordIndex, Equiv.symm_apply_apply, finiteAddress_eq_sum]
  unfold ExternalProjection.wordTranslation projectedDigit
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro position _
  ring

/-- Failure of frequent arbitrarily fast collisions gives a fixed exponential
lower bound at every sufficiently large level, hence at infinitely many levels. -/
theorem exponentialSeparation_of_not_collision (ratio slope : ℝ)
    (hgood : slope ∉ ExceptionalSlopes.frequentCollisionSlopes (planarTranslation ratio)) :
    ExternalProjection.HasExponentialSeparation ratio (projectedDigit ratio slope) := by
  change ¬ (∀ rate : ℝ, 0 < rate → ∀ first : ℕ, ∃ depth, first ≤ depth ∧
    ∃ left right : Fin (4 ^ depth), left ≠ right ∧
      |((planarTranslation ratio depth left).2 - (planarTranslation ratio depth right).2) -
        slope * ((planarTranslation ratio depth left).1 -
          (planarTranslation ratio depth right).1)| < rate ^ depth) at hgood
  push_neg at hgood
  rcases hgood with ⟨rate, hrate, first, hseparated⟩
  refine ⟨rate, hrate, ?_⟩
  apply Filter.Eventually.frequently
  filter_upwards [eventually_ge_atTop first] with depth hdepth
  intro left right hdifferent
  rw [projected_word_eq, projected_word_eq]
  have h := hseparated depth hdepth (wordIndex left) (wordIndex right)
    (fun hequal => hdifferent (wordIndex_injective depth hequal))
  convert h using 1 <;> congr 1 <;> ring

end LambdaCantor.First.PrefixSlopes
