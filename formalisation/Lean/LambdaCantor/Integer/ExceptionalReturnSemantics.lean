import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic

namespace LambdaCantor.Integer.Exceptional

def returnLevel (offset : Fin 4 → ℝ) : List (Fin 4) → ℝ → ℝ
  | [], level => level
  | digit :: remaining, level => returnLevel offset remaining (3 * level - offset digit)

/-- A disagreement before either word ends certifies incomparable cylinders. -/
def WordsSeparate (first second : List (Fin 4)) : Prop :=
  ∃ index, index < first.length ∧ index < second.length ∧
    first.getD index 0 ≠ second.getD index 0

theorem wordsSeparate_cons {first second : List (Fin 4)}
    (separated : WordsSeparate first second) (digit : Fin 4) :
    WordsSeparate (digit :: first) (digit :: second) := by
  obtain ⟨index, first_bound, second_bound, different⟩ := separated
  refine ⟨index + 1, by simpa using Nat.succ_lt_succ first_bound,
    by simpa using Nat.succ_lt_succ second_bound, ?_⟩
  simpa using different

theorem wordsSeparate_distinct_heads (first second : List (Fin 4))
    (firstDigit secondDigit : Fin 4) (different : firstDigit ≠ secondDigit) :
    WordsSeparate (firstDigit :: first) (secondDigit :: second) := by
  exact ⟨0, by simp, by simp, by simpa using different⟩

def OneReturn (offset : Fin 4 → ℝ) (target : Set ℝ) (depth : ℕ) (level : ℝ) : Prop :=
  ∃ word : List (Fin 4), word.length ≤ depth ∧ returnLevel offset word level ∈ target

def TwoReturns (offset : Fin 4 → ℝ) (target : Set ℝ) (depth : ℕ) (level : ℝ) : Prop :=
  ∃ first second : List (Fin 4), first.length ≤ depth ∧ second.length ≤ depth ∧
    WordsSeparate first second ∧ returnLevel offset first level ∈ target ∧
      returnLevel offset second level ∈ target

theorem oneReturn_stop (offset : Fin 4 → ℝ) (target : Set ℝ) (level : ℝ)
    (inside : level ∈ target) : OneReturn offset target 0 level :=
  ⟨[], by simp, inside⟩

theorem OneReturn.mono {offset : Fin 4 → ℝ} {target : Set ℝ} {depth later : ℕ}
    {level : ℝ} (witness : OneReturn offset target depth level) (bound : depth ≤ later) :
    OneReturn offset target later level := by
  obtain ⟨word, length_bound, inside⟩ := witness
  exact ⟨word, length_bound.trans bound, inside⟩

theorem TwoReturns.mono {offset : Fin 4 → ℝ} {target : Set ℝ} {depth later : ℕ}
    {level : ℝ} (witness : TwoReturns offset target depth level) (bound : depth ≤ later) :
    TwoReturns offset target later level := by
  obtain ⟨first, second, first_bound, second_bound, separated, first_inside, second_inside⟩ := witness
  exact ⟨first, second, first_bound.trans bound, second_bound.trans bound,
    separated, first_inside, second_inside⟩

theorem OneReturn.lift {offset : Fin 4 → ℝ} {target : Set ℝ} {depth : ℕ}
    {level : ℝ} (digit : Fin 4)
    (witness : OneReturn offset target depth (3 * level - offset digit)) :
    OneReturn offset target (depth + 1) level := by
  obtain ⟨word, length_bound, inside⟩ := witness
  exact ⟨digit :: word, by simpa using Nat.succ_le_succ length_bound, inside⟩

theorem TwoReturns.lift {offset : Fin 4 → ℝ} {target : Set ℝ} {depth : ℕ}
    {level : ℝ} (digit : Fin 4)
    (witness : TwoReturns offset target depth (3 * level - offset digit)) :
    TwoReturns offset target (depth + 1) level := by
  obtain ⟨first, second, first_bound, second_bound, separated, first_inside, second_inside⟩ := witness
  exact ⟨digit :: first, digit :: second, by simpa using Nat.succ_le_succ first_bound,
    by simpa using Nat.succ_le_succ second_bound, wordsSeparate_cons separated digit,
    first_inside, second_inside⟩

theorem twoReturns_of_distinct_children {offset : Fin 4 → ℝ} {target : Set ℝ}
    {depth : ℕ} {level : ℝ} (firstDigit secondDigit : Fin 4)
    (different : firstDigit ≠ secondDigit)
    (first_witness : OneReturn offset target depth (3 * level - offset firstDigit))
    (second_witness : OneReturn offset target depth (3 * level - offset secondDigit)) :
    TwoReturns offset target (depth + 1) level := by
  obtain ⟨first, first_bound, first_inside⟩ := first_witness
  obtain ⟨second, second_bound, second_inside⟩ := second_witness
  exact ⟨firstDigit :: first, secondDigit :: second,
    by simpa using Nat.succ_le_succ first_bound,
    by simpa using Nat.succ_le_succ second_bound,
    wordsSeparate_distinct_heads first second firstDigit secondDigit different,
    first_inside, second_inside⟩

end LambdaCantor.Integer.Exceptional
