import LambdaCantor.Last.ReturnWords
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
namespace LambdaCantor.Last

theorem cantorDust_first_child {ratio : ℝ} (hratio : 0 ≤ ratio) (hless : ratio < 1)
    {point : ℝ × ℝ} (hpoint : point ∈ cantorDust ratio) :
    ∃ digit : Bool × Bool, ∃ tail : ℝ × ℝ, tail ∈ cantorDust ratio ∧
      wordMap ratio [digit] tail = point := by
  have hfirst := hpoint.1
  have hsecond := hpoint.2
  rw [cantorSet_selfsimilar hratio hless] at hfirst hsecond
  rcases hfirst with ⟨first, hfirst, hfirst_eq⟩ | ⟨first, hfirst, hfirst_eq⟩ <;>
    rcases hsecond with ⟨second, hsecond, hsecond_eq⟩ | ⟨second, hsecond, hsecond_eq⟩
  · refine ⟨(false, false), (first, second), ⟨hfirst, hsecond⟩, ?_⟩
    ext <;> simp [wordMap, digitPoint, ← hfirst_eq, ← hsecond_eq]
  · refine ⟨(false, true), (first, second), ⟨hfirst, hsecond⟩, ?_⟩
    ext <;> simp [wordMap, digitPoint, ← hfirst_eq, ← hsecond_eq]
  · refine ⟨(true, false), (first, second), ⟨hfirst, hsecond⟩, ?_⟩
    ext <;> simp [wordMap, digitPoint, ← hfirst_eq, ← hsecond_eq]
  · refine ⟨(true, true), (first, second), ⟨hfirst, hsecond⟩, ?_⟩
    ext <;> simp [wordMap, digitPoint, ← hfirst_eq, ← hsecond_eq]

theorem exists_wordCylinder_at_depth {ratio : ℝ} (hratio : 0 ≤ ratio) (hless : ratio < 1)
    (depth : ℕ) {point : ℝ × ℝ} (hpoint : point ∈ cantorDust ratio) :
    ∃ word : List (Bool × Bool), word.length = depth ∧ point ∈ wordCylinder ratio word := by
  induction depth generalizing point with
  | zero => exact ⟨[], rfl, point, hpoint, rfl⟩
  | succ depth induction_hypothesis =>
    obtain ⟨digit, tail, htail, hrepresentation⟩ := cantorDust_first_child hratio hless hpoint
    obtain ⟨word, hlength, source, hsource, hsource_eq⟩ := induction_hypothesis htail
    refine ⟨digit :: word, by simp [hlength], source, hsource, ?_⟩
    change (1 - ratio) • digitPoint digit + ratio • wordMap ratio word source = point
    rw [hsource_eq]
    exact hrepresentation

theorem wordsDiverge_of_length_eq {first second : List (Bool × Bool)}
    (hlength : first.length = second.length) (hdifferent : first ≠ second) :
    WordsDiverge first second := by
  induction first generalizing second with
  | nil => cases second <;> simp_all
  | cons firstDigit firstRest induction_hypothesis =>
    cases second with
    | nil => simp at hlength
    | cons secondDigit secondRest =>
      by_cases hdigits : firstDigit = secondDigit
      · subst secondDigit
        have hrest : firstRest ≠ secondRest := by
          intro equality
          exact hdifferent (congrArg (List.cons firstDigit) equality)
        obtain ⟨common, leftDigit, rightDigit, leftRest, rightRest,
          different, hfirst, hsecond⟩ := induction_hypothesis (by simpa using hlength) hrest
        refine ⟨firstDigit :: common, leftDigit, rightDigit, leftRest, rightRest,
          different, ?_, ?_⟩ <;> simp [hfirst, hsecond]
      · exact ⟨[], firstDigit, secondDigit, firstRest, secondRest, hdigits, rfl, rfl⟩

/-- Product cylinders are relatively open in the dust; their quantitative
separation also covers words that end at cylinder endpoints. -/
theorem isOpen_wordCylinder_in_dust {ratio : ℝ} (hpositive : 0 < ratio)
    (hhalf : ratio < 1 / 2) (word : List (Bool × Bool)) :
    IsOpen {point : cantorDust ratio | point.val ∈ wordCylinder ratio word} := by
  apply Metric.isOpen_iff.mpr
  intro point hpoint
  refine ⟨(1 - 2 * ratio) * ratio ^ word.length,
    mul_pos (by linarith) (pow_pos hpositive _), ?_⟩
  intro other hother
  obtain ⟨otherWord, hlength, hmembership⟩ :=
    exists_wordCylinder_at_depth hpositive.le (by linarith) word.length other.property
  by_cases hequal : word = otherWord
  · simpa [hequal] using hmembership
  · obtain ⟨firstTail, hfirstTail, hfirst_eq⟩ := hpoint
    obtain ⟨secondTail, hsecondTail, hsecond_eq⟩ := hmembership
    have hgap := diverging_words_distance_gap hpositive hhalf word otherWord
      (wordsDiverge_of_length_eq hlength.symm hequal) word.length le_rfl hfirstTail hsecondTail
    rw [hfirst_eq, hsecond_eq] at hgap
    have hnear : dist other.val point.val < (1 - 2 * ratio) * ratio ^ word.length := hother
    rw [dist_comm] at hnear
    exact False.elim ((not_lt_of_ge hgap) hnear)

theorem wordMap_injective {ratio : ℝ} (hpositive : 0 < ratio)
    (word : List (Bool × Bool)) : Function.Injective (wordMap ratio word) := by
  intro first second hequal
  apply dist_eq_zero.mp
  have hzero : dist (wordMap ratio word first) (wordMap ratio word second) = 0 := by
    rw [hequal, dist_self]
  rw [wordMap_distance, abs_of_pos hpositive] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hpositive.ne')

end LambdaCantor.Last
