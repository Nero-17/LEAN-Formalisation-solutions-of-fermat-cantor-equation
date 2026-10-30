import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
namespace LambdaCantor.Integer
/-- Base-four encoding labels (0,1,r,r+1); position zero is the first digit. -/
def wordDigit (word position : ℕ) : ℕ := word / 4 ^ (4 - position) % 4

def prefixA (word : ℕ) : ℕ → ℤ
  | 0 => 0
  | j + 1 => 3 * prefixA word j + (wordDigit word j / 2 : ℕ)
def prefixB (word : ℕ) : ℕ → ℤ
  | 0 => 0
  | j + 1 => 3 * prefixB word j + (wordDigit word j % 2 : ℕ)
def lowerCoefficient (digit : ℕ) : ℤ × ℤ :=
  if digit = 0 then (0,0) else if digit = 1 then (1,1)
  else if digit = 2 then (1,3) else (3,1)
def upperCoefficient (digit : ℕ) : ℤ × ℤ :=
  if digit = 0 then (0,2) else if digit = 1 then (2,0)
  else if digit = 2 then (2,2) else (3,3)
/-- Numerators over the common positive denominator 6*3^4. -/
def pulledLower (word j : ℕ) : ℤ × ℤ :=
  ((6 * prefixA word j + (lowerCoefficient (wordDigit word j)).1) * 3^(4-j),
   (6 * prefixB word j + (lowerCoefficient (wordDigit word j)).2) * 3^(4-j))
def pulledUpper (word j : ℕ) : ℤ × ℤ :=
  ((6 * prefixA word j + (upperCoefficient (wordDigit word j)).1) * 3^(4-j),
   (6 * prefixB word j + (upperCoefficient (wordDigit word j)).2) * 3^(4-j))
def discrepancy (word j k : ℕ) : ℤ × ℤ :=
  ((pulledLower word j).1 - (pulledUpper word k).1,
   (pulledLower word j).2 - (pulledUpper word k).2)
def Feasible (word : ℕ) (slope : ℝ) : Prop :=
  ∀ j k : Fin 5, (discrepancy word j.val k.val).1 * slope +
    (discrepancy word j.val k.val).2 ≤ 0

/-- A rational linear constraint is violated throughout an open band if
its endpoint values are nonnegative and at least one is positive. -/
theorem positive_inside_band (a b lower upper slope : ℝ)
    (hlo : lower < slope) (hhi : slope < upper)
    (hl : 0 ≤ a * lower + b) (hu : 0 ≤ a * upper + b)
    (strict : 0 < a * lower + b ∨ 0 < a * upper + b) :
    0 < a * slope + b := by
  rcases le_total 0 a with ha | ha
  · by_cases hzero : a = 0
    · subst a; simpa using strict
    · have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
      nlinarith
  · by_cases hzero : a = 0
    · subst a; simpa using strict
    · have hneg : a < 0 := lt_of_le_of_ne ha hzero
      nlinarith
end LambdaCantor.Integer
