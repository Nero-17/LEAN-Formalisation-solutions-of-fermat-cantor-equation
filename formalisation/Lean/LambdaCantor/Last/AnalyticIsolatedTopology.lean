import LambdaCantor.Last.CylinderTopology

noncomputable section
namespace LambdaCantor.Last

/-- Relative isolation in the actual fibre makes every sufficiently small
containing product cylinder a singleton fibre. The proof includes boundary
points of cylinders and uses the actual quantitative cylinder diameter. -/
theorem isolated_fibre_eventually_singleton_cylinders {ratio : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2)
    (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (point : {value | value ∈ cantorDust ratio ∧ function value = level})
    (isolated : IsOpen ({point} : Set {value | value ∈ cantorDust ratio ∧ function value = level})) :
    ∃ cutoff : ℕ, ∀ word : List (Bool × Bool), cutoff ≤ word.length →
      point.val ∈ wordCylinder ratio word →
      ∀ other : ℝ × ℝ, other ∈ cantorDust ratio → function other = level →
        other ∈ wordCylinder ratio word → other = point.val := by
  obtain ⟨radius, radius_positive, neighbourhood⟩ := Metric.isOpen_iff.mp isolated point (by simp)
  have less_one : ratio < 1 := by linarith
  obtain ⟨cutoff, scale_small⟩ := exists_pow_lt_of_lt_one radius_positive less_one
  refine ⟨cutoff, ?_⟩
  intro word word_large point_in_word other other_in_dust other_level other_in_word
  have distance_bound := wordCylinder_dist_le positive.le less_one word other_in_word point_in_word
  have scale_bound : ratio ^ word.length ≤ ratio ^ cutoff :=
    pow_le_pow_of_le_one positive.le less_one.le word_large
  have near : dist other point.val < radius := distance_bound.trans_lt (scale_bound.trans_lt scale_small)
  have nearby : (⟨other, other_in_dust, other_level⟩ :
      {value | value ∈ cantorDust ratio ∧ function value = level}) ∈ Metric.ball point radius := near
  have singleton := neighbourhood nearby
  exact congrArg Subtype.val (Set.mem_singleton_iff.mp singleton)

/-- Child-hull filling turns actual local fibre isolation into the unique
closed-child condition. A contact at another child's hull endpoint is ruled
out by the same argument as an interior contact. -/
theorem isolated_fibre_unique_filled_child {ratio : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2)
    (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (point : {value | value ∈ cantorDust ratio ∧ function value = level})
    (isolated : IsOpen ({point} : Set {value | value ∈ cantorDust ratio ∧ function value = level}))
    (filled : ∀ word : List (Bool × Bool), ∀ digit : Bool × Bool,
      level ∈ Set.Icc (function (wordMap ratio word (wordMap ratio [digit] 0)))
        (function (wordMap ratio word (wordMap ratio [digit] (1,1)))) →
      ∃ tail ∈ cantorDust ratio,
        function (wordMap ratio word (wordMap ratio [digit] tail)) = level) :
    ∃ cutoff : ℕ, ∀ word : List (Bool × Bool), cutoff ≤ word.length →
      ∀ actual : Bool × Bool, ∀ tail ∈ cantorDust ratio,
        wordMap ratio word (wordMap ratio [actual] tail) = point.val →
      ∀ other : Bool × Bool, other ≠ actual →
        level ∉ Set.Icc (function (wordMap ratio word (wordMap ratio [other] 0)))
          (function (wordMap ratio word (wordMap ratio [other] (1,1)))) := by
  have less_one : ratio < 1 := by linarith
  obtain ⟨cutoff, singleton⟩ := isolated_fibre_eventually_singleton_cylinders
    positive less_half function level point isolated
  refine ⟨cutoff, ?_⟩
  intro word word_large actual tail tail_in_dust actual_eq other different hull_membership
  obtain ⟨other_tail, other_tail_in_dust, other_level⟩ := filled word other hull_membership
  have actual_in_word : point.val ∈ wordCylinder ratio word :=
    ⟨wordMap ratio [actual] tail, wordMap_mem_dust positive.le less_one _ tail_in_dust, actual_eq⟩
  have other_child_in_dust := wordMap_mem_dust positive.le less_one [other] other_tail_in_dust
  have other_in_dust := wordMap_mem_dust positive.le less_one word other_child_in_dust
  have other_eq := singleton word word_large actual_in_word
    (wordMap ratio word (wordMap ratio [other] other_tail)) other_in_dust other_level
    ⟨wordMap ratio [other] other_tail, other_child_in_dust, rfl⟩
  have child_eq : wordMap ratio [other] other_tail = wordMap ratio [actual] tail :=
    wordMap_injective positive word (other_eq.trans actual_eq.symm)
  have separated := first_digit_distance_gap positive.le less_one other actual different
    other_tail_in_dust tail_in_dust
  rw [child_eq, dist_self] at separated
  linarith

end LambdaCantor.Last
