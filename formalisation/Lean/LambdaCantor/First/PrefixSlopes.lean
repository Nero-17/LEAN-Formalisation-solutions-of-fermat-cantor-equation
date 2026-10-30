import LambdaCantor.First.ExceptionalSlopes

/-! Instantiation of the exceptional-slope theorem by the actual finite
translations of the ratio-Cantor dust. -/

noncomputable section
namespace LambdaCantor.First.PrefixSlopes

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

def extendWord {depth : ℕ} (word : Fin depth → Bool) (position : ℕ) : Bool :=
  if hposition : position < depth then word ⟨position, hposition⟩ else false

def finiteAddress (ratio : ℝ) {depth : ℕ} (word : Fin depth → Bool) : ℝ :=
  address ratio (extendWord word)

theorem finiteAddress_injective {ratio : ℝ} (hratio : 0 < ratio)
    (hhalf : ratio < 1 / 2) (depth : ℕ) :
    Function.Injective (finiteAddress ratio (depth := depth)) := by
  intro left right hequal
  have hextended := address_injective hratio hhalf hequal
  funext position
  have h := congrFun hextended (position : ℕ)
  simpa only [extendWord, dif_pos position.isLt] using h

/-- A slightly weaker form of the source's level separation, with exponent
`depth` instead of `depth-1`, avoids a special zero-depth convention. -/
theorem finiteAddress_gap {ratio : ℝ} (hratio : 0 < ratio)
    (hhalf : ratio < 1 / 2) {depth : ℕ} (left right : Fin depth → Bool)
    (hdifferent : finiteAddress ratio left ≠ finiteAddress ratio right) :
    (1 - 2 * ratio) * ratio ^ depth ≤
      |finiteAddress ratio left - finiteAddress ratio right| := by
  have hword : left ≠ right := by
    intro hequal
    exact hdifferent (congrArg (finiteAddress ratio) hequal)
  have hexists : ∃ position : ℕ, position < depth ∧
      extendWord left position ≠ extendWord right position := by
    by_contra hnone
    apply hword
    funext position
    by_contra hneq
    apply hnone
    exact ⟨position, position.isLt, by simpa [extendWord, position.isLt] using hneq⟩
  have hseparation := prefix_separation hratio hhalf (extendWord left) (extendWord right)
    (Nat.find hexists) (fun position hbefore => ?_) (Nat.find_spec hexists).2
  · have hpower : ratio ^ depth ≤ ratio ^ Nat.find hexists :=
      pow_le_pow_of_le_one hratio.le (by linarith) (Nat.find_spec hexists).1.le
    exact (mul_le_mul_of_nonneg_left hpower (by linarith : 0 ≤ 1 - 2 * ratio)).trans hseparation
  · by_contra hneq
    exact Nat.find_min hexists hbefore
      ⟨hbefore.trans (Nat.find_spec hexists).1, hneq⟩

def planarWordEquiv (depth : ℕ) : (Fin depth → Bool × Bool) ≃ Fin (4 ^ depth) :=
  Fintype.equivFinOfCardEq (by simp [Fintype.card_fun])

def planarTranslation (ratio : ℝ) (depth : ℕ) (index : Fin (4 ^ depth)) : ℝ × ℝ :=
  (finiteAddress ratio (fun position => ((planarWordEquiv depth).symm index position).1),
   finiteAddress ratio (fun position => ((planarWordEquiv depth).symm index position).2))

theorem planarTranslation_injective {ratio : ℝ} (hratio : 0 < ratio)
    (hhalf : ratio < 1 / 2) (depth : ℕ) : Function.Injective (planarTranslation ratio depth) := by
  intro left right hequal
  apply (planarWordEquiv depth).symm.injective
  funext position
  apply Prod.ext
  · have hfirst := finiteAddress_injective hratio hhalf depth (congrArg Prod.fst hequal)
    exact congrFun hfirst position
  · have hsecond := finiteAddress_injective hratio hhalf depth (congrArg Prod.snd hequal)
    exact congrFun hsecond position

theorem planarTranslation_horizontal_gap {ratio : ℝ} (hratio : 0 < ratio)
    (hhalf : ratio < 1 / 2) (depth : ℕ) (left right : Fin (4 ^ depth))
    (hdifferent : (planarTranslation ratio depth left).1 ≠ (planarTranslation ratio depth right).1) :
    (1 - 2 * ratio) * ratio ^ depth ≤
      |(planarTranslation ratio depth left).1 - (planarTranslation ratio depth right).1| :=
  finiteAddress_gap hratio hhalf _ _ hdifferent

theorem planarTranslation_vertical_gap {ratio : ℝ} (hratio : 0 < ratio)
    (hhalf : ratio < 1 / 2) (depth : ℕ) (left right : Fin (4 ^ depth))
    (hdifferent : (planarTranslation ratio depth left).2 ≠ (planarTranslation ratio depth right).2) :
    (1 - 2 * ratio) * ratio ^ depth ≤
      |(planarTranslation ratio depth left).2 - (planarTranslation ratio depth right).2| :=
  finiteAddress_gap hratio hhalf _ _ hdifferent

/-- The exceptional set of projected finite translations of the actual
Cantor dust is zero dimensional. No separation or dimension hypothesis on
these arrays is left to the caller. -/
theorem cantor_projection_collision_slopes_dimension_zero
    {ratio : ℝ} (hratio : 0 < ratio) (hhalf : ratio < 1 / 2) :
    dimH (ExceptionalSlopes.frequentCollisionSlopes (planarTranslation ratio)) = 0 :=
  ExceptionalSlopes.frequentCollisionSlopes_dimension_zero
    (planarTranslation ratio) hratio (by linarith : 0 < 1 - 2 * ratio)
    (planarTranslation_injective hratio hhalf)
    (planarTranslation_horizontal_gap hratio hhalf)
    (planarTranslation_vertical_gap hratio hhalf)

end LambdaCantor.First.PrefixSlopes
