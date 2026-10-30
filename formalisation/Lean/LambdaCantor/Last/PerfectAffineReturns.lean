import LambdaCantor.Last.PerfectAffineLevels
import Mathlib.Topology.MetricSpace.Perfect

noncomputable section
namespace LambdaCantor.Last

theorem linearWordReturn_child_interior {ratio slope level : ℝ} (hpositive : 0 < ratio)
    (digit : Bool × Bool)
    (hreturn : linearWordReturn ratio (positiveLinear slope) [digit] level ∈ Set.Ioo 0 (1 + slope)) :
    level ∈ Set.Ioo (positiveLinear slope (wordMap ratio [digit] 0))
      (positiveLinear slope (wordMap ratio [digit] 0) + ratio * (1 + slope)) := by
  have hnormalized : 0 < (level - positiveLinear slope (wordMap ratio [digit] 0)) / ratio ∧
      (level - positiveLinear slope (wordMap ratio [digit] 0)) / ratio < 1 + slope := by
    simpa only [linearWordReturn, returnLevel, List.length_singleton, pow_one, Set.mem_Ioo] using hreturn
  have hlower := (lt_div_iff₀ hpositive).mp hnormalized.1
  have hupper := (div_lt_iff₀ hpositive).mp hnormalized.2
  constructor <;> nlinarith

theorem perfect_affine_branch_mem_interior_core {ratio slope level : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2) (hslope : 0 < slope)
    (perfectSubset : Set (ℝ × ℝ)) (hperfect : Perfect perfectSubset)
    (hsubset : perfectSubset ⊆
      {value | value ∈ cantorDust ratio ∧ positiveLinear slope value = level})
    (word : List (Bool × Bool)) (firstDigit secondDigit : Bool × Bool)
    (hdifferent : firstDigit ≠ secondDigit)
    (first second : ℝ × ℝ) (hfirst : first ∈ cantorDust ratio) (hsecond : second ∈ cantorDust ratio)
    (hfirst_perfect : wordMap ratio word (wordMap ratio [firstDigit] first) ∈ perfectSubset)
    (hsecond_perfect : wordMap ratio word (wordMap ratio [secondDigit] second) ∈ perfectSubset) :
    linearWordReturn ratio (positiveLinear slope) word level ∈ interior (affineOverlapCore ratio slope) := by
  have hfirst_return := linearWordReturn_mem_Ioo_of_perfect hpositive hhalf hslope
    perfectSubset hperfect hsubset hfirst_perfect (word ++ [firstDigit])
    (by exact ⟨first, hfirst, by rw [wordMap_append]⟩)
  have hsecond_return := linearWordReturn_mem_Ioo_of_perfect hpositive hhalf hslope
    perfectSubset hperfect hsubset hsecond_perfect (word ++ [secondDigit])
    (by exact ⟨second, hsecond, by rw [wordMap_append]⟩)
  rw [linearWordReturn_append ratio hpositive.ne'] at hfirst_return hsecond_return
  have hfirst_interval := linearWordReturn_child_interior hpositive firstDigit hfirst_return
  have hsecond_interval := linearWordReturn_child_interior hpositive secondDigit hsecond_return
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset ((isOpen_Ioo.inter isOpen_Ioo).mem_nhds
    ⟨hfirst_interval, hsecond_interval⟩)
  intro value membership
  apply mem_affineOverlapCore.mpr
  exact ⟨firstDigit, secondDigit, hdifferent,
    ⟨membership.1.1.le, membership.1.2.le⟩, ⟨membership.2.1.le, membership.2.2.le⟩⟩

/-- A nonempty perfect affine fibre supplies two incomparable strict returns
to the complete closed-overlap core. -/
theorem perfect_affine_fibre_strict_returns {ratio slope level : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2) (hslope : 0 < slope)
    (perfectSubset : Set (ℝ × ℝ)) (hperfect : Perfect perfectSubset)
    (hnonempty : perfectSubset.Nonempty)
    (hsubset : perfectSubset ⊆
      {value | value ∈ cantorDust ratio ∧ positiveLinear slope value = level}) :
    ∃ pair : ReturnPair,
      linearWordReturn ratio (positiveLinear slope) (pair.word false) level ∈
        interior (affineOverlapCore ratio slope) ∧
      linearWordReturn ratio (positiveLinear slope) (pair.word true) level ∈
        interior (affineOverlapCore ratio slope) := by
  obtain ⟨point, hpoint⟩ := hnonempty
  obtain ⟨common, _, firstDigit, secondDigit, hdifferent, first, second,
    hfirst, hsecond, hfirst_perfect, hsecond_perfect⟩ :=
    perfect_fibre_branching_extension hpositive hhalf (positiveLinear slope) level
      perfectSubset hperfect hsubset hpoint [] ⟨point, (hsubset hpoint).1, rfl⟩
  simp only [List.nil_append] at hfirst_perfect hsecond_perfect
  have hfirst_word : wordMap ratio common (wordMap ratio [firstDigit] first) ∈
      wordCylinder ratio (common ++ [firstDigit]) := ⟨first, hfirst, by rw [wordMap_append]⟩
  have hsecond_word : wordMap ratio common (wordMap ratio [secondDigit] second) ∈
      wordCylinder ratio (common ++ [secondDigit]) := ⟨second, hsecond, by rw [wordMap_append]⟩
  obtain ⟨firstSuffix, _, firstLeft, firstRight, hfirst_different,
    firstLeftTail, firstRightTail, hfirst_left, hfirst_right, hfirst_left_perfect, hfirst_right_perfect⟩ :=
    perfect_fibre_branching_extension hpositive hhalf (positiveLinear slope) level
      perfectSubset hperfect hsubset hfirst_perfect (common ++ [firstDigit]) hfirst_word
  obtain ⟨secondSuffix, _, secondLeft, secondRight, hsecond_different,
    secondLeftTail, secondRightTail, hsecond_left, hsecond_right, hsecond_left_perfect, hsecond_right_perfect⟩ :=
    perfect_fibre_branching_extension hpositive hhalf (positiveLinear slope) level
      perfectSubset hperfect hsubset hsecond_perfect (common ++ [secondDigit]) hsecond_word
  let pair : ReturnPair := {
    word := fun bit => if bit then (common ++ [secondDigit]) ++ secondSuffix
      else (common ++ [firstDigit]) ++ firstSuffix
    length_pos := by intro bit; cases bit <;> simp
    diverge := by
      refine ⟨common, firstDigit, secondDigit, firstSuffix, secondSuffix, hdifferent, ?_, ?_⟩ <;>
        simp [List.append_assoc] }
  refine ⟨pair, ?_, ?_⟩
  · exact perfect_affine_branch_mem_interior_core hpositive hhalf hslope perfectSubset hperfect hsubset
      ((common ++ [firstDigit]) ++ firstSuffix) firstLeft firstRight hfirst_different
      firstLeftTail firstRightTail hfirst_left hfirst_right hfirst_left_perfect hfirst_right_perfect
  · exact perfect_affine_branch_mem_interior_core hpositive hhalf hslope perfectSubset hperfect hsubset
      ((common ++ [secondDigit]) ++ secondSuffix) secondLeft secondRight hsecond_different
      secondLeftTail secondRightTail hsecond_left hsecond_right hsecond_left_perfect hsecond_right_perfect

theorem affine_fibre_strict_returns_of_uncountable {ratio slope level : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2) (hslope : 0 < slope)
    (huncountable : ¬ {value | value ∈ cantorDust ratio ∧ positiveLinear slope value = level}.Countable) :
    ∃ pair : ReturnPair,
      linearWordReturn ratio (positiveLinear slope) (pair.word false) level ∈
        interior (affineOverlapCore ratio slope) ∧
      linearWordReturn ratio (positiveLinear slope) (pair.word true) level ∈
        interior (affineOverlapCore ratio slope) := by
  have hclosed : IsClosed {value | value ∈ cantorDust ratio ∧ positiveLinear slope value = level} :=
    (isCompact_cantorDust hpositive.le (by linarith)).isClosed.inter
      (isClosed_eq (positiveLinearContinuous slope).continuous continuous_const)
  obtain ⟨perfectSubset, hperfect, hnonempty, hsubset⟩ :=
    exists_perfect_nonempty_of_isClosed_of_not_countable hclosed huncountable
  exact perfect_affine_fibre_strict_returns hpositive hhalf hslope perfectSubset hperfect hnonempty hsubset

end LambdaCantor.Last
