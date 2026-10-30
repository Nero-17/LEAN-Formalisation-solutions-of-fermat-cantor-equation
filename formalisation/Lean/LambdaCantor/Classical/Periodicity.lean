import LambdaCantor.Integer.Feasibility
import LambdaCantor.Integer.Windows
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity

noncomputable section
namespace LambdaCantor.Classical
open LambdaCantor.Integer

theorem original_band_subset_first_band {slope : ℝ}
    (lower : 11 / 9 < slope) (upper : slope < 2027 / 1624) :
    89 / 73 < slope ∧ slope < 171 / 137 := by
  constructor <;> linarith

theorem wordWindow_digit (digits : ℕ → Fin 4) (n : ℕ) (j : Fin 5) :
    wordDigit (wordWindow digits n).val j.val = (digits (n + j.val)).val := by
  have decoding (a b c d e : Fin 4) :
      let word := 4 * (64 * a.val + 16 * b.val + 4 * c.val + d.val) + e.val
      word / 256 % 4 = a.val ∧ word / 64 % 4 = b.val ∧
        word / 16 % 4 = c.val ∧ word / 4 % 4 = d.val ∧ word % 4 = e.val := by
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    have hd := d.isLt
    have he := e.isLt
    dsimp
    omega
  have decoded := decoding (digits n) (digits (n+1)) (digits (n+2))
    (digits (n+3)) (digits (n+4))
  fin_cases j
  · simpa [wordDigit, wordWindow, vertexWindow] using decoded.1
  · simpa [wordDigit, wordWindow, vertexWindow] using decoded.2.1
  · simpa [wordDigit, wordWindow, vertexWindow] using decoded.2.2.1
  · simpa [wordDigit, wordWindow, vertexWindow] using decoded.2.2.2.1
  · simpa [wordDigit, wordWindow, vertexWindow] using decoded.2.2.2.2

/-- Pulling the exact recurrence back to the initial tail. -/
theorem recurrence_prefix (word : ℕ) (slope : ℝ) (tail : ℕ → ℝ)
    (recurrence : ∀ j < 4, tail (j + 1) = 3 * tail j -
      ((wordDigit word j / 2 : ℕ) : ℝ) * slope -
      ((wordDigit word j % 2 : ℕ) : ℝ)) (j : ℕ) (bound : j ≤ 4) :
    tail j = 3 ^ j * tail 0 - (prefixA word j : ℝ) * slope -
      (prefixB word j : ℝ) := by
  induction j with
  | zero => simp [prefixA, prefixB]
  | succ j ih =>
    rw [recurrence j (by omega), ih (by omega)]
    simp only [prefixA, prefixB, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast, pow_succ]
    ring

/-- A uniform error bound on five exclusive domains bounds all pulled-back
feasibility gaps. The factor 972 is twice their common denominator 486. -/
theorem approximate_discrepancy (word : ℕ) (slope error : ℝ) (tail : ℕ → ℝ)
    (error_nonnegative : 0 ≤ error)
    (recurrence : ∀ j < 4, tail (j + 1) = 3 * tail j -
      ((wordDigit word j / 2 : ℕ) : ℝ) * slope -
      ((wordDigit word j % 2 : ℕ) : ℝ))
    (lower : ∀ j : Fin 5,
      (lowerCoefficient (wordDigit word j.val)).1 * slope +
        (lowerCoefficient (wordDigit word j.val)).2 ≤ 6 * (tail j.val + error))
    (upper : ∀ j : Fin 5,
      6 * (tail j.val - error) ≤
      (upperCoefficient (wordDigit word j.val)).1 * slope +
        (upperCoefficient (wordDigit word j.val)).2) (j k : Fin 5) :
    (discrepancy word j.val k.val).1 * slope +
      (discrepancy word j.val k.val).2 ≤ 972 * error := by
  have lower_pulled : ∀ j : Fin 5,
      (pulledLower word j.val).1 * slope + (pulledLower word j.val).2 ≤
        486 * tail 0 + 486 * error := by
    intro j
    have domain := lower j
    rw [recurrence_prefix word slope tail recurrence j.val (by omega)] at domain
    fin_cases j <;>
      norm_num [pulledLower] at domain ⊢ <;> push_cast <;> nlinarith
  have upper_pulled : ∀ k : Fin 5,
      486 * tail 0 - 486 * error ≤
        (pulledUpper word k.val).1 * slope + (pulledUpper word k.val).2 := by
    intro k
    have domain := upper k
    rw [recurrence_prefix word slope tail recurrence k.val (by omega)] at domain
    fin_cases k <;>
      norm_num [pulledUpper] at domain ⊢ <;> push_cast <;> nlinarith
  have first := lower_pulled j
  have second := upper_pulled k
  simp only [discrepancy, Int.cast_sub]
  linarith

def windowError (errors : ℕ → ℝ) (n : ℕ) : ℝ :=
  errors n + errors (n+1) + errors (n+2) + errors (n+3) + errors (n+4)

theorem windowError_nonnegative (errors : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ errors n)
    (n : ℕ) : 0 ≤ windowError errors n := by
  unfold windowError
  linarith [nonnegative n, nonnegative (n+1), nonnegative (n+2),
    nonnegative (n+3), nonnegative (n+4)]

theorem error_le_windowError (errors : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ errors n)
    (n : ℕ) (j : Fin 5) : errors (n+j.val) ≤ windowError errors n := by
  have h0 := nonnegative n
  have h1 := nonnegative (n+1)
  have h2 := nonnegative (n+2)
  have h3 := nonnegative (n+3)
  have h4 := nonnegative (n+4)
  fin_cases j <;> simp only [windowError, Nat.add_zero] <;> linarith

theorem scaled_windowError_vanishes (errors : ℕ → ℝ)
    (vanishing : ∀ ε > 0, ∃ start, ∀ n ≥ start, errors n < ε) :
    ∀ ε > 0, ∃ start, ∀ n ≥ start, 972 * windowError errors n < ε := by
  intro ε positive
  obtain ⟨start, bound⟩ := vanishing (ε / 4860) (by positivity)
  refine ⟨start, ?_⟩
  intro n hn
  have h0 := bound n hn
  have h1 := bound (n+1) (by omega)
  have h2 := bound (n+2) (by omega)
  have h3 := bound (n+3) (by omega)
  have h4 := bound (n+4) (by omega)
  unfold windowError
  linarith

theorem sequence_approximate_discrepancy (digits : ℕ → Fin 4)
    (slope : ℝ) (tails errors : ℕ → ℝ)
    (nonnegative : ∀ n, 0 ≤ errors n)
    (recurrence : ∀ n, tails (n+1) = 3 * tails n -
      (((digits n).val / 2 : ℕ) : ℝ) * slope - (((digits n).val % 2 : ℕ) : ℝ))
    (lower : ∀ n, (lowerCoefficient (digits n).val).1 * slope +
      (lowerCoefficient (digits n).val).2 ≤ 6 * (tails n + errors n))
    (upper : ∀ n, 6 * (tails n - errors n) ≤
      (upperCoefficient (digits n).val).1 * slope + (upperCoefficient (digits n).val).2)
    (n : ℕ) (j k : Fin 5) :
    (discrepancy (wordWindow digits n).val j.val k.val).1 * slope +
      (discrepancy (wordWindow digits n).val j.val k.val).2 ≤
        972 * windowError errors n := by
  apply approximate_discrepancy (wordWindow digits n).val slope (windowError errors n)
    (fun t => tails (n+t)) (windowError_nonnegative errors nonnegative n)
  · intro t ht
    have digit_eq := wordWindow_digit digits n (⟨t, by omega⟩ : Fin 5)
    simp only [Fin.val_mk] at digit_eq
    rw [digit_eq]
    exact (by simpa [Nat.add_assoc] using recurrence (n+t))
  · intro t
    rw [wordWindow_digit]
    have domain := lower (n+t.val)
    have bound := error_le_windowError errors nonnegative n t
    linarith
  · intro t
    rw [wordWindow_digit]
    have domain := upper (n+t.val)
    have bound := error_le_windowError errors nonnegative n t
    linarith

end LambdaCantor.Classical
