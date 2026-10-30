import Mathlib.Data.Int.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Choose
import Lean.Elab.Tactic.Omega

namespace LambdaCantor.Last

def EventuallyPeriodicIntegerSequence (digits : ℕ → ℤ) : Prop :=
  ∃ prefixLength period : ℕ, 0 < period ∧
    ∀ index, digits (index+prefixLength+period) = digits (index+prefixLength)

/-- The exact-double special case of Condition (*)w with w=2: prefixes
contain two consecutive identical words, the prefixLength/word length ratio is
bounded, and word lengths increase strictly. -/
def DoubleStammering (digits : ℕ → ℤ) : Prop :=
  ¬ EventuallyPeriodicIntegerSequence digits ∧
    ∃ starts lengths : ℕ → ℕ, ∃ bound : ℕ,
      StrictMono lengths ∧ ∀ index,
        0 < lengths index ∧ starts index ≤ bound*lengths index ∧
          ∀ offset < lengths index,
            digits (starts index+lengths index+offset) = digits (starts index+offset)

def IntegerAlternatingBlock (digits : ℕ → ℤ) (start length : ℕ) : Prop :=
  ∀ offset, offset+1 < length →
    digits (start+offset+1)+digits (start+offset)=1

theorem alternating_block_even_repeat (digits : ℕ → ℤ) {start length halfLength : ℕ}
    (alternating : IntegerAlternatingBlock digits start length)
    (fits : 4*halfLength ≤ length) :
    ∀ offset < 2*halfLength,
      digits (start+2*halfLength+offset) = digits (start+offset) := by
  intro offset offset_bound
  have period_two : ∀ position, position+2 < length →
      digits (start+position+2)=digits (start+position) := by
    intro position position_bound
    have first := alternating position (by omega)
    have second : digits (start+position+2)+digits (start+position+1)=1 := by
      simpa [Nat.add_assoc] using alternating (position+1) (by omega)
    omega
  have repeated : ∀ count, count ≤ halfLength →
      digits (start+offset+2*count)=digits (start+offset) := by
    intro count
    induction count with
    | zero => simp
    | succ count induction =>
      intro count_bound
      have previous := induction (by omega)
      have next := period_two (offset+2*count) (by omega)
      have first_eq : start+(offset+2*count)+2 = start+offset+2*(count+1) := by omega
      have second_eq : start+(offset+2*count) = start+offset+2*count := by omega
      rw [first_eq, second_eq] at next
      exact next.trans previous
  have final := repeated halfLength le_rfl
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using final

/-- The shadowing blocks in the boundary-phase argument imply the precise
stammering hypothesis internally: a block starting at n and having length
at least n−fixedLoss contains a repeated even word comparable in length to n.
No digit theorem is assumed in this combinatorial step. -/
theorem doubleStammering_of_long_alternating_blocks (digits : ℕ → ℤ)
    (nonperiodic : ¬ EventuallyPeriodicIntegerSequence digits)
    (fixedLoss : ℕ)
    (blocks : ∀ threshold : ℕ, ∃ start : ℕ, threshold ≤ start ∧
      IntegerAlternatingBlock digits start (start-fixedLoss)) :
    DoubleStammering digits := by
  classical
  choose select selected_lower selected_block using blocks
  let starts : ℕ → ℕ := fun index =>
    Nat.rec (select (2*fixedLoss+8))
      (fun _ previous => select (max (2*fixedLoss+8) (4*previous+fixedLoss+8))) index
  let lengths : ℕ → ℕ := fun index => 2*((starts index-fixedLoss)/4)
  have starts_lower : ∀ index, 2*fixedLoss+8 ≤ starts index := by
    intro index
    cases index with
    | zero => exact selected_lower _
    | succ index => exact (le_max_left _ _).trans (selected_lower _)
  have starts_step : ∀ index, 4*starts index+fixedLoss+8 ≤ starts (index+1) := by
    intro index
    exact (le_max_right _ _).trans (selected_lower _)
  have starts_block : ∀ index,
      IntegerAlternatingBlock digits (starts index) (starts index-fixedLoss) := by
    intro index
    cases index with
    | zero => exact selected_block _
    | succ index => exact selected_block _
  refine ⟨nonperiodic, starts, lengths, 8, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro index
    have lower := starts_step index
    dsimp [lengths]
    omega
  · intro index
    have lower := starts_lower index
    refine ⟨?_, ?_, ?_⟩
    · dsimp [lengths]
      omega
    · dsimp [lengths]
      omega
    · exact alternating_block_even_repeat digits (starts_block index) (by omega)

end LambdaCantor.Last
