import LambdaCantor.Last.CylinderTopology
import LambdaCantor.Last.TangentSource
import Mathlib.Topology.Perfect

noncomputable section
open scoped Topology
namespace LambdaCantor.Last

theorem perfect_cylinder_has_distinct {ratio : ℝ} (hpositive : 0 < ratio)
    (hhalf : ratio < 1 / 2) (perfectSubset : Set (ℝ × ℝ))
    (hperfect : Perfect perfectSubset) (hsubset : perfectSubset ⊆ cantorDust ratio)
    {point : ℝ × ℝ} (hpoint : point ∈ perfectSubset)
    (word : List (Bool × Bool)) (hword : point ∈ wordCylinder ratio word) :
    ∃ other ∈ perfectSubset, other ∈ wordCylinder ratio word ∧ other ≠ point := by
  obtain ⟨radius, hradius, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_wordCylinder_in_dust hpositive hhalf word)
    (⟨point, hsubset hpoint⟩ : cantorDust ratio) hword
  obtain ⟨other, ⟨hother_near, hother_perfect⟩, hother_different⟩ :=
    (preperfect_iff_nhds.mp hperfect.acc) point hpoint (Metric.ball point radius)
      (Metric.ball_mem_nhds point hradius)
  refine ⟨other, hother_perfect, ?_, hother_different⟩
  exact hball (show (⟨other, hsubset hother_perfect⟩ : cantorDust ratio) ∈
    Metric.ball (⟨point, hsubset hpoint⟩ : cantorDust ratio) radius from hother_near)

/-- Both branches can be witnessed inside the original perfect subset. -/
theorem perfect_fibre_branching_extension {ratio : ℝ} (hpositive : 0 < ratio)
    (hhalf : ratio < 1 / 2) (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (perfectSubset : Set (ℝ × ℝ)) (hperfect : Perfect perfectSubset)
    (hsubset : perfectSubset ⊆ {value | value ∈ cantorDust ratio ∧ function value = level})
    {point : ℝ × ℝ} (hpoint : point ∈ perfectSubset)
    (initialWord : List (Bool × Bool)) (hinitial_point : point ∈ wordCylinder ratio initialWord) :
    ∃ suffix : List (Bool × Bool), point ∈ wordCylinder ratio (initialWord ++ suffix) ∧
      ∃ firstDigit secondDigit : Bool × Bool, firstDigit ≠ secondDigit ∧
        ∃ first second : ℝ × ℝ, first ∈ cantorDust ratio ∧ second ∈ cantorDust ratio ∧
          wordMap ratio (initialWord ++ suffix) (wordMap ratio [firstDigit] first) ∈ perfectSubset ∧
          wordMap ratio (initialWord ++ suffix) (wordMap ratio [secondDigit] second) ∈ perfectSubset := by
  have hless : ratio < 1 := by linarith
  obtain ⟨other, hother_perfect, hinitial_other, hother_different⟩ :=
    perfect_cylinder_has_distinct hpositive hhalf perfectSubset hperfect
      (fun value membership => (hsubset membership).1) hpoint initialWord hinitial_point
  obtain ⟨firstTail, hfirstTail, hfirst_eq⟩ := hinitial_point
  obtain ⟨secondTail, hsecondTail, hsecond_eq⟩ := hinitial_other
  have htail_different : firstTail ≠ secondTail := by
    intro equality
    apply hother_different
    rw [← hsecond_eq, ← hfirst_eq, equality]
  have hdistance : 0 < dist firstTail secondTail := dist_pos.mpr htail_different
  obtain ⟨depth, hdepth⟩ :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hpositive.le hless).eventually
      (gt_mem_nhds hdistance)).exists
  obtain ⟨firstWord, hfirst_length, hfirst_cell⟩ :=
    exists_wordCylinder_at_depth hpositive.le hless depth hfirstTail
  obtain ⟨secondWord, hsecond_length, hsecond_cell⟩ :=
    exists_wordCylinder_at_depth hpositive.le hless depth hsecondTail
  have hwords_different : firstWord ≠ secondWord := by
    intro equality
    have hbound := wordCylinder_dist_le hpositive.le hless firstWord hfirst_cell
      (by simpa [equality] using hsecond_cell)
    rw [hfirst_length] at hbound
    exact (not_lt_of_ge hbound) hdepth
  obtain ⟨common, firstDigit, secondDigit, firstRest, secondRest,
    hdifferent, hfirst_word, hsecond_word⟩ :=
    wordsDiverge_of_length_eq (hfirst_length.trans hsecond_length.symm) hwords_different
  obtain ⟨firstSource, hfirstSource, hfirst_source_eq⟩ := hfirst_cell
  obtain ⟨secondSource, hsecondSource, hsecond_source_eq⟩ := hsecond_cell
  have hfirst_inner : wordMap ratio common
      (wordMap ratio [firstDigit] (wordMap ratio firstRest firstSource)) = firstTail := by
    change wordMap ratio common (wordMap ratio (firstDigit :: firstRest) firstSource) = firstTail
    rw [← wordMap_append, ← hfirst_word]
    exact hfirst_source_eq
  have hsecond_inner : wordMap ratio common
      (wordMap ratio [secondDigit] (wordMap ratio secondRest secondSource)) = secondTail := by
    change wordMap ratio common (wordMap ratio (secondDigit :: secondRest) secondSource) = secondTail
    rw [← wordMap_append, ← hsecond_word]
    exact hsecond_source_eq
  have hfirst_representation : wordMap ratio (initialWord ++ common)
      (wordMap ratio [firstDigit] (wordMap ratio firstRest firstSource)) = point := by
    rw [wordMap_append, hfirst_inner]
    exact hfirst_eq
  have hsecond_representation : wordMap ratio (initialWord ++ common)
      (wordMap ratio [secondDigit] (wordMap ratio secondRest secondSource)) = other := by
    rw [wordMap_append, hsecond_inner]
    exact hsecond_eq
  refine ⟨common, ?_, ?_⟩
  · exact ⟨_, wordMap_mem_dust hpositive.le hless _
      (wordMap_mem_dust hpositive.le hless _ hfirstSource), hfirst_representation⟩
  · refine ⟨firstDigit, secondDigit, hdifferent,
      wordMap ratio firstRest firstSource, wordMap ratio secondRest secondSource,
      wordMap_mem_dust hpositive.le hless _ hfirstSource,
      wordMap_mem_dust hpositive.le hless _ hsecondSource, ?_, ?_⟩
    · rw [hfirst_representation]
      exact hpoint
    · rw [hsecond_representation]
      exact hother_perfect

theorem perfect_fibre_deep_branching_with_points {ratio : ℝ} (hpositive : 0 < ratio)
    (hhalf : ratio < 1 / 2) (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (perfectSubset : Set (ℝ × ℝ)) (hperfect : Perfect perfectSubset)
    (hsubset : perfectSubset ⊆ {value | value ∈ cantorDust ratio ∧ function value = level})
    {point : ℝ × ℝ} (hpoint : point ∈ perfectSubset) (minimumDepth : ℕ) :
    ∃ word : List (Bool × Bool), minimumDepth ≤ word.length ∧
      point ∈ wordCylinder ratio word ∧
      ∃ firstDigit secondDigit : Bool × Bool, firstDigit ≠ secondDigit ∧
        ∃ first second : ℝ × ℝ, first ∈ cantorDust ratio ∧ second ∈ cantorDust ratio ∧
          wordMap ratio word (wordMap ratio [firstDigit] first) ∈ perfectSubset ∧
          wordMap ratio word (wordMap ratio [secondDigit] second) ∈ perfectSubset := by
  obtain ⟨initialWord, hinitial_length, hinitial_point⟩ :=
    exists_wordCylinder_at_depth hpositive.le (by linarith) minimumDepth (hsubset hpoint).1
  obtain ⟨suffix, hword, hbranches⟩ := perfect_fibre_branching_extension hpositive hhalf
    function level perfectSubset hperfect hsubset hpoint initialWord hinitial_point
  exact ⟨initialWord ++ suffix, by simp only [List.length_append, hinitial_length]; omega,
    hword, hbranches⟩

/-- Every point of a perfect actual fibre has arbitrarily deep genuine
branching cylinders. Relative openness of product cylinders is essential here. -/
theorem perfect_fibre_deep_branching {ratio : ℝ} (hpositive : 0 < ratio)
    (hhalf : ratio < 1 / 2) (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (perfectSubset : Set (ℝ × ℝ)) (hperfect : Perfect perfectSubset)
    (hsubset : perfectSubset ⊆ {value | value ∈ cantorDust ratio ∧ function value = level})
    {point : ℝ × ℝ} (hpoint : point ∈ perfectSubset) (minimumDepth : ℕ) :
    ∃ word : List (Bool × Bool), minimumDepth ≤ word.length ∧
      point ∈ wordCylinder ratio word ∧ BranchingCylinder ratio function level word := by
  obtain ⟨word, hdepth, hword, firstDigit, secondDigit, hdifferent,
    first, second, hfirst, hsecond, hfirst_perfect, hsecond_perfect⟩ :=
    perfect_fibre_deep_branching_with_points hpositive hhalf function level
      perfectSubset hperfect hsubset hpoint minimumDepth
  exact ⟨word, hdepth, hword, firstDigit, secondDigit, hdifferent,
    first, second, hfirst, hsecond, (hsubset hfirst_perfect).2, (hsubset hsecond_perfect).2⟩

end LambdaCantor.Last
