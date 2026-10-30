import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
namespace LambdaCantor.Classical

def TernaryZeroOne (number : ℕ) : Prop :=
  ∀ position : ℕ, (number / 3 ^ position) % 3 ≤ 1

lemma ternaryZeroOne_div_nine {number : ℕ} (digits : TernaryZeroOne number) :
    TernaryZeroOne (number / 9) := by
  intro position
  have h := digits (position + 2)
  simpa [Nat.div_div_eq_div_mul, pow_add, Nat.mul_comm] using h

lemma square_product_descent {number coefficient root : ℕ}
    (digits : TernaryZeroOne number) (coefficient_mod : coefficient % 3 = 2)
    (equation : number * coefficient = root ^ 2) :
    number % 9 = 0 ∧ root % 3 = 0 := by
  have digit0 := digits 0
  have digit1 := digits 1
  simp only [pow_zero, Nat.div_one, pow_one] at digit0 digit1
  have residues_three := congrArg (fun n : ℕ => n % 3) equation
  simp only [Nat.mul_mod, Nat.pow_mod, Nat.mod_mod, coefficient_mod] at residues_three
  have number_mod_three : number % 3 = 0 := by
    have root_bound : root % 3 < 3 := Nat.mod_lt _ (by omega)
    interval_cases first : number % 3 <;> interval_cases second : root % 3 <;>
      norm_num at *
  have root_mod_three : root % 3 = 0 := by
    rw [number_mod_three] at residues_three
    have root_bound : root % 3 < 3 := Nat.mod_lt _ (by omega)
    interval_cases second : root % 3 <;> norm_num at *
  have residues := congrArg (fun n : ℕ => n % 9) equation
  simp only [Nat.mul_mod, Nat.pow_mod, Nat.mod_mod] at residues
  simp only [Nat.mod_mod] at residues
  have hn : number % 9 < 9 := Nat.mod_lt _ (by omega)
  have hc : coefficient % 9 < 9 := Nat.mod_lt _ (by omega)
  have hr : root % 9 < 9 := Nat.mod_lt _ (by omega)
  have hn0 : number % 9 % 3 ≤ 1 := by omega
  have hn1 : number % 9 / 3 ≤ 1 := by omega
  have hc0 : coefficient % 9 % 3 = 2 := by omega
  constructor
  · have root_square : (root % 9) ^ 2 % 9 = 0 := by
      interval_cases hr' : root % 9 <;> norm_num at * <;> omega
    rw [root_square] at residues
    interval_cases hn' : number % 9 <;> interval_cases hc' : coefficient % 9 <;>
      norm_num at * <;> omega
  · exact root_mod_three

theorem ternary_square_product_zero {number coefficient root : ℕ}
    (digits : TernaryZeroOne number) (coefficient_mod : coefficient % 3 = 2)
    (equation : number * coefficient = root ^ 2) : number = 0 := by
  induction number using Nat.strong_induction_on generalizing root with
  | h number inductionHypothesis =>
    by_cases zero : number = 0
    · exact zero
    have divisibility := square_product_descent digits coefficient_mod equation
    have number_decomposition : number = 9 * (number / 9) := by omega
    have root_decomposition : root = 3 * (root / 3) := by omega
    have reduced_equation : number / 9 * coefficient = (root / 3) ^ 2 := by
      rw [number_decomposition, root_decomposition] at equation
      nlinarith [equation]
    have reduced_zero := inductionHypothesis (number / 9) (by omega)
      (ternaryZeroOne_div_nine digits) reduced_equation
    omega

/-- Finite ternary words with digits zero and one, including leading zeroes. -/
inductive ZeroOneWord : ℕ → ℕ → Prop
  | nil : ZeroOneWord 0 0
  | zero {length number} : ZeroOneWord length number → ZeroOneWord (length + 1) (3 * number)
  | one {length number} : ZeroOneWord length number → ZeroOneWord (length + 1) (3 * number + 1)

def repunit : ℕ → ℕ
  | 0 => 0
  | length + 1 => 3 * repunit length + 1

theorem ZeroOneWord.le_repunit {length number : ℕ} (word : ZeroOneWord length number) :
    number ≤ repunit length := by
  induction word with
  | nil => simp [repunit]
  | zero word ih => simp only [repunit]; omega
  | one word ih => simp only [repunit]; omega

theorem ZeroOneWord.complement {length number : ℕ} (word : ZeroOneWord length number) :
    ZeroOneWord length (repunit length - number) := by
  induction word with
  | nil => exact .nil
  | @zero length number word ih =>
    have bound := word.le_repunit
    convert ZeroOneWord.one ih using 1 <;> simp only [repunit] <;> omega
  | @one length number word ih =>
    have bound := word.le_repunit
    convert ZeroOneWord.zero ih using 1 <;> simp only [repunit] <;> omega

theorem ternaryZeroOne_prepend {number digit : ℕ} (digits : TernaryZeroOne number)
    (digit_bound : digit ≤ 1) : TernaryZeroOne (3 * number + digit) := by
  intro position
  cases position with
  | zero => simp only [pow_zero, Nat.div_one]; omega
  | succ position =>
    rw [pow_succ, Nat.mul_comm (3 ^ position) 3, ← Nat.div_div_eq_div_mul]
    have quotient : (3 * number + digit) / 3 = number := by omega
    rw [quotient]
    exact digits position

theorem ZeroOneWord.digits {length number : ℕ} (word : ZeroOneWord length number) :
    TernaryZeroOne number := by
  induction word with
  | nil => intro position; simp
  | zero word ih => simpa using ternaryZeroOne_prepend ih (show 0 ≤ 1 by omega)
  | one word ih => exact ternaryZeroOne_prepend ih (by omega)

theorem repunit_mod_three {length : ℕ} (positive : 0 < length) : repunit length % 3 = 1 := by
  cases length with
  | zero => omega
  | succ length => simp [repunit]

theorem repunit_formula (length : ℕ) : 2 * repunit length + 1 = 3 ^ length := by
  induction length with
  | zero => simp [repunit]
  | succ length ih => simp only [repunit, pow_succ]; omega

theorem zeroOneWord_circle_axis_of_mod_one {length first second : ℕ}
    (positive : 0 < length) (first_word : ZeroOneWord length first)
    (first_mod : first % 3 = 1)
    (equation : first ^ 2 + second ^ 2 = repunit length ^ 2) :
    first = repunit length ∧ second = 0 := by
  have bound := first_word.le_repunit
  have subtraction := Nat.sub_add_cancel bound
  have product : (repunit length - first) * (repunit length + first) = second ^ 2 := by
    nlinarith
  have coefficient_mod : (repunit length + first) % 3 = 2 := by
    simp [Nat.add_mod, repunit_mod_three positive, first_mod]
  have complement_zero := ternary_square_product_zero first_word.complement.digits
    coefficient_mod product
  constructor <;> nlinarith

/-- The exact finite-word obstruction underlying the rational-circle lemma. -/
theorem zeroOneWord_circle_axes {length first second : ℕ}
    (first_word : ZeroOneWord length first) (second_word : ZeroOneWord length second)
    (equation : first ^ 2 + second ^ 2 = repunit length ^ 2) :
    (first = 0 ∧ second = repunit length) ∨
      (first = repunit length ∧ second = 0) := by
  by_cases positive : 0 < length
  · have first_digit := first_word.digits 0
    have second_digit := second_word.digits 0
    simp only [pow_zero, Nat.div_one] at first_digit second_digit
    have residues := congrArg (fun number : ℕ => number % 3) equation
    simp only [Nat.add_mod, Nat.pow_mod, Nat.mod_mod, repunit_mod_three positive] at residues
    have one : first % 3 = 1 ∨ second % 3 = 1 := by
      by_contra contradiction
      have hf : first % 3 = 0 := by omega
      have hs : second % 3 = 0 := by omega
      norm_num [hf, hs] at residues
    rcases one with first_mod | second_mod
    · exact Or.inr (zeroOneWord_circle_axis_of_mod_one positive first_word first_mod equation)
    · have swapped : second ^ 2 + first ^ 2 = repunit length ^ 2 := by omega
      have result := zeroOneWord_circle_axis_of_mod_one positive second_word second_mod swapped
      exact Or.inl ⟨result.2, result.1⟩
  · have length_zero : length = 0 := by omega
    subst length
    have first_bound := first_word.le_repunit
    have second_bound := second_word.le_repunit
    simp only [repunit] at *
    exact Or.inl ⟨by omega, by omega⟩

end LambdaCantor.Classical


