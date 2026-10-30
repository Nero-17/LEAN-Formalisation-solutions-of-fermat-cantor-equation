import LambdaCantor.Last.ReturnState

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

structure ReturnPair where
  word : Bool → List (Bool × Bool)
  length_pos : ∀ bit, 0 < (word bit).length
  diverge : WordsDiverge (word false) (word true)

def linearWordReturn (ratio : ℝ) (linear : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (word : List (Bool × Bool)) (level : ℝ) : ℝ :=
  returnLevel (ratio ^ word.length) level (linear (wordMap ratio word 0))

theorem continuous_linearWordReturn (ratio : ℝ) (linear : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (word : List (Bool × Bool)) : Continuous (linearWordReturn ratio linear word) :=
  (continuous_id.sub continuous_const).div_const _

theorem linearWordReturn_append (ratio : ℝ) (hratio : ratio ≠ 0)
    (linear : (ℝ × ℝ) →ₗ[ℝ] ℝ) (first second : List (Bool × Bool)) (level : ℝ) :
    linearWordReturn ratio linear (first ++ second) level =
      linearWordReturn ratio linear second (linearWordReturn ratio linear first level) := by
  unfold linearWordReturn returnLevel
  rw [wordMap_append, wordMap_affine ratio first (wordMap ratio second 0)]
  simp only [List.length_append, pow_add, map_add, map_smul, smul_eq_mul]
  field_simp
  <;> ring

/-- The finite, uniformly robust data extracted from compact strict returns. -/
structure FiniteReturnAtlas (ratio : ℝ) (linear : (ℝ × ℝ) →ₗ[ℝ] ℝ) (levels : Set ℝ) where
  pair : levels → ReturnPair
  maxDepth : ℕ
  length_le : ∀ level bit, ((pair level).word bit).length ≤ maxDepth
  margin : ℝ
  margin_pos : 0 < margin
  robust : ∀ level : levels, ∀ values : Bool → ℝ,
    (∀ bit, dist (values bit) (linearWordReturn ratio linear ((pair level).word bit) level) < margin) →
    ∀ bit, values bit ∈ levels

theorem exists_finiteReturnAtlas (ratio : ℝ) (linear : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (levels : Set ℝ) (hcompact : IsCompact levels) (hnonempty : levels.Nonempty)
    (hcomplement : levelsᶜ.Nonempty)
    (hreturns : ∀ level ∈ levels, ∃ pair : ReturnPair,
      linearWordReturn ratio linear (pair.word false) level ∈ interior levels ∧
      linearWordReturn ratio linear (pair.word true) level ∈ interior levels) :
    Nonempty (FiniteReturnAtlas ratio linear levels) := by
  classical
  obtain ⟨selected, margin, neighborhood, hmargin, hopen, hsubset, hselected⟩ :=
    compact_strict_return_selection hcompact hnonempty hcomplement
      (fun pair : ReturnPair => linearWordReturn ratio linear (pair.word false))
      (fun pair : ReturnPair => linearWordReturn ratio linear (pair.word true))
      (fun pair => continuous_linearWordReturn ratio linear _)
      (fun pair => continuous_linearWordReturn ratio linear _) hreturns
  let chosen : levels → ReturnPair := fun level => (hselected level (hsubset level.property)).choose
  have chosen_mem (level : levels) : chosen level ∈ selected :=
    (hselected level (hsubset level.property)).choose_spec.1
  refine ⟨{
    pair := chosen
    maxDepth := selected.sup (fun pair => max (pair.word false).length (pair.word true).length)
    length_le := ?_
    margin := margin
    margin_pos := hmargin
    robust := ?_ }⟩
  · intro level bit
    have hbound := Finset.le_sup (f := fun pair : ReturnPair =>
      max (pair.word false).length (pair.word true).length) (chosen_mem level)
    cases bit
    · exact (le_max_left _ _).trans hbound
    · exact (le_max_right _ _).trans hbound
  · intro level values hvalues bit
    have hrobust := (hselected level (hsubset level.property)).choose_spec.2
      (values false) (values true) (hvalues false) (hvalues true)
    cases bit
    · exact hrobust.1
    · exact hrobust.2

namespace ReturnState
variable {levels : Set ℝ} {bound : ℝ≥0}

theorem nextLevel_close (ratio : ℝ) (hpositive : 0 < ratio) (hless : ratio < 1)
    (linear : (ℝ × ℝ) →ₗ[ℝ] ℝ) (state : ReturnState levels bound)
    (word : List (Bool × Bool)) (margin : ℝ) (maxDepth : ℕ)
    (hmargin : 0 < margin) (hdepth : word.length ≤ maxDepth)
    (hsmall : (bound : ℝ) < margin * ratio ^ maxDepth) :
    dist (state.nextLevel ratio linear word) (linearWordReturn ratio linear word state.level) < margin := by
  have hcorner : wordMap ratio word 0 ∈ cantorDust ratio :=
    wordMap_mem_dust hpositive.le hless word ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩
  have herror := error_lt_margin_mul_scale ratio margin bound
    (state.error (wordMap ratio word 0)) word.length maxDepth hpositive hless.le hdepth hmargin hsmall
    (state.error_abs_le_on_dust ratio hpositive.le hless hcorner)
  rw [Real.dist_eq]
  have hdifference : state.nextLevel ratio linear word -
      linearWordReturn ratio linear word state.level =
      -state.error (wordMap ratio word 0) / ratio ^ word.length := by
    unfold nextLevel linearWordReturn returnLevel
    ring
  rw [hdifference, abs_div, abs_neg, abs_of_pos (pow_pos hpositive _),
    div_lt_iff₀ (pow_pos hpositive _)]
  exact herror

end ReturnState

namespace FiniteReturnAtlas
variable {ratio : ℝ} {linear : (ℝ × ℝ) →ₗ[ℝ] ℝ} {levels : Set ℝ}

def system (atlas : FiniteReturnAtlas ratio linear levels)
    (hpositive : 0 < ratio) (hless : ratio < 1) (bound : ℝ≥0)
    (hsmall : (bound : ℝ) < atlas.margin * ratio ^ atlas.maxDepth) :
    AdaptiveWordSystem (ReturnState levels bound) :=
  normalizedReturnSystem ratio hpositive linear levels bound
    (fun state bit => (atlas.pair ⟨state.level, state.level_mem⟩).word bit)
    atlas.maxDepth (fun state bit => (atlas.pair ⟨state.level, state.level_mem⟩).length_pos bit)
    (fun state bit => atlas.length_le ⟨state.level, state.level_mem⟩ bit)
    (fun state => atlas.robust ⟨state.level, state.level_mem⟩
      (fun bit => state.nextLevel ratio linear ((atlas.pair ⟨state.level, state.level_mem⟩).word bit))
      (fun bit => state.nextLevel_close ratio hpositive hless linear _ atlas.margin atlas.maxDepth
        atlas.margin_pos (atlas.length_le _ bit) hsmall))

end FiniteReturnAtlas
end LambdaCantor.Last
