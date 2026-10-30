import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace LambdaCantor.Integer

/-- A sound integer interval union checker. Intervals may overlap or be
redundant; the frontier never decreases. -/
def intervalCoverScan : List (ℤ × ℤ) → ℤ → ℤ → Bool
  | [], frontier, target => decide (target ≤ frontier)
  | (lower,upper)::rest, frontier, target =>
      decide (lower ≤ frontier) && intervalCoverScan rest (max frontier upper) target

theorem intervalCoverScan_sound (intervals : List (ℤ × ℤ)) (frontier target : ℤ)
    (checked : intervalCoverScan intervals frontier target = true) :
    ∀ x : ℝ, (frontier : ℝ) < x → x ≤ (target : ℝ) →
      ∃ interval ∈ intervals, (interval.1 : ℝ) ≤ x ∧ x ≤ (interval.2 : ℝ) := by
  induction intervals generalizing frontier with
  | nil =>
    simp only [intervalCoverScan, decide_eq_true_eq] at checked
    intro x hlo hhi
    have hc : (target : ℝ) ≤ frontier := by exact_mod_cast checked
    linarith
  | cons interval rest ih =>
    rcases interval with ⟨lower, upper⟩
    simp only [intervalCoverScan, Bool.and_eq_true, decide_eq_true_eq] at checked
    intro x hlo hhi
    by_cases hu : x ≤ (upper : ℝ)
    · refine ⟨(lower,upper), by simp, ?_, hu⟩
      have hl : (lower : ℝ) ≤ frontier := by exact_mod_cast checked.1
      linarith
    · have hm : ((max frontier upper : ℤ) : ℝ) < x := by
        rcases le_total frontier upper with h | h
        · rw [max_eq_right h]
          exact lt_of_not_ge hu
        · rw [max_eq_left h]
          exact hlo
      obtain ⟨interval, hmem, hl, hu⟩ := ih (max frontier upper) checked.2 x hm hhi
      exact ⟨interval, List.mem_cons_of_mem _ hmem, hl, hu⟩

/-- Add an explicitly checked covering interval at the left endpoint. -/
theorem closed_integer_cover_sound (intervals : List (ℤ × ℤ)) (left right : ℤ)
    (checked : intervalCoverScan intervals left right = true)
    (left_covered : ∃ interval ∈ intervals, interval.1 ≤ left ∧ left ≤ interval.2) :
    ∀ x : ℝ, (left : ℝ) ≤ x → x ≤ (right : ℝ) →
      ∃ interval ∈ intervals, (interval.1 : ℝ) ≤ x ∧ x ≤ (interval.2 : ℝ) := by
  intro x hlo hhi
  rcases eq_or_lt_of_le hlo with h | h
  · obtain ⟨interval, hmem, h₁, h₂⟩ := left_covered
    refine ⟨interval, hmem, ?_, ?_⟩
    · rw [← h]; exact_mod_cast h₁
    · rw [← h]; exact_mod_cast h₂
  · exact intervalCoverScan_sound intervals left right checked x h hhi

end LambdaCantor.Integer
