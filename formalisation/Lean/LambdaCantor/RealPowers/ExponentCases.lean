import LambdaCantor.Common
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace LambdaCantor.RealPowers

/-- The integer exceptional list is separate from the seven noninteger
rational exceptions. Neither list is replaced by the old five slope bands. -/
def integerExceptionalExponents : List ℕ := [9,10,23,25,28,31,32,78,82]

def rationalExceptionalPairs : List (ℕ × ℕ) :=
  [(24,23),(19,18),(13,12),(8,7),(8,3),(11,4),(53,2)]

inductive IntegerExponentCase (exponent : ℕ) : Prop
  | quadratic (equal : exponent = 2)
  | cubic (equal : exponent = 3)
  | exceptional (member : exponent ∈ integerExceptionalExponents)
  | ordinarySmall (lower : 4 ≤ exponent) (upper : exponent ≤ 300)
      (not_exceptional : exponent ∉ integerExceptionalExponents)
  | large (lower : 301 ≤ exponent)

theorem integer_exponent_cases (exponent : ℕ) (lower : 2 ≤ exponent) : IntegerExponentCase exponent := by
  by_cases quadratic : exponent = 2
  · exact .quadratic quadratic
  by_cases cubic : exponent = 3
  · exact .cubic cubic
  by_cases large : 301 ≤ exponent
  · exact .large large
  by_cases exceptional : exponent ∈ integerExceptionalExponents
  · exact .exceptional exceptional
  · exact .ordinarySmall (by omega) (by omega) exceptional

/-- Exhaustive top-level branches for Section 3.1. This classification theorem
contains no dimension hypotheses. Actual assembly must discharge every branch:
IrrationalPositive; Integer.IntegerPowers (including circle/cubic/nine DAGs);
LargeDenominatorPositive; the finite low-denominator partition and seven DAGs;
and LargeExponent grouped layers/tail. -/
inductive RealExponentCase (exponent : ℝ) : Prop
  | irrational (proof : Irrational exponent)
  | integer (numerator : ℕ) (lower : 2 ≤ numerator) (equal : exponent = numerator)
  | largeDenominator (numerator denominator : ℕ) (coprime : numerator.Coprime denominator)
      (lower : 110 ≤ denominator) (equal : exponent = (numerator : ℝ)/denominator)
  | exceptionalRational (numerator denominator : ℕ) (coprime : numerator.Coprime denominator)
      (member : (numerator,denominator) ∈ rationalExceptionalPairs)
      (equal : exponent = (numerator : ℝ)/denominator)
  | finiteLowDenominator (numerator denominator : ℕ) (coprime : numerator.Coprime denominator)
      (denominator_lower : 2 ≤ denominator) (denominator_upper : denominator ≤ 109)
      (numerator_lower : denominator < numerator) (numerator_upper : numerator < 2187*denominator)
      (not_exceptional : (numerator,denominator) ∉ rationalExceptionalPairs)
      (equal : exponent = (numerator : ℝ)/denominator)
  | largeExponent (numerator denominator : ℕ) (coprime : numerator.Coprime denominator)
      (denominator_lower : 2 ≤ denominator) (denominator_upper : denominator ≤ 109)
      (exponent_lower : (2187 : ℝ) ≤ (numerator : ℝ)/denominator)
      (equal : exponent = (numerator : ℝ)/denominator)

/-- Reduced rational representation uses its actual positive numerator and
denominator. The b=1 integer branch is explicitly retained. -/
theorem real_exponent_cases (exponent : ℝ) (exponent_gt_one : 1 < exponent) : RealExponentCase exponent := by
  by_cases irrational : Irrational exponent
  · exact .irrational irrational
  obtain ⟨rational, rational_equal⟩ := exists_rat_of_not_irrational irrational
  have rational_positive : (0 : ℚ) < rational := by
    have real_positive : (0 : ℝ) < rational := by rw [← rational_equal]; linarith
    exact_mod_cast real_positive
  have numerator_positive : 0 < rational.num := Rat.num_pos.mpr rational_positive
  have numerator_cast : ((rational.num.natAbs : ℕ) : ℝ) = (rational.num : ℝ) := by
    have integer_cast : (rational.num.natAbs : ℤ) = rational.num := by
      rw [Int.natCast_natAbs, abs_of_nonneg numerator_positive.le]
    simpa only [Int.cast_natCast] using congrArg (fun value : ℤ => (value : ℝ)) integer_cast
  have representation : exponent = (rational.num.natAbs : ℝ)/rational.den := by
    rw [rational_equal, Rat.cast_def, numerator_cast]
  have denominator_positive : 0 < rational.den := rational.pos
  have denominator_real_positive : (0 : ℝ) < rational.den := by exact_mod_cast denominator_positive
  by_cases integer : rational.den = 1
  · have exponent_equal : exponent = (rational.num.natAbs : ℝ) := by simpa only [integer, Nat.cast_one, div_one] using representation
    have numerator_lower : 2 ≤ rational.num.natAbs := by
      have lower : (1 : ℝ) < rational.num.natAbs := by rwa [← exponent_equal]
      have lower_nat : 1 < rational.num.natAbs := by exact_mod_cast lower
      omega
    exact .integer rational.num.natAbs numerator_lower exponent_equal
  by_cases large_denominator : 110 ≤ rational.den
  · exact .largeDenominator rational.num.natAbs rational.den rational.reduced large_denominator representation
  have denominator_lower : 2 ≤ rational.den := by omega
  have denominator_upper : rational.den ≤ 109 := by omega
  by_cases bounded : exponent < 2187
  · have numerator_lower : rational.den < rational.num.natAbs := by
      have cleared := (lt_div_iff₀ denominator_real_positive).mp (representation ▸ exponent_gt_one)
      have real_lower : (rational.den : ℝ) < rational.num.natAbs := by simpa only [one_mul] using cleared
      exact_mod_cast real_lower
    have numerator_upper : rational.num.natAbs < 2187*rational.den := by
      have cleared := (div_lt_iff₀ denominator_real_positive).mp (representation ▸ bounded)
      exact_mod_cast cleared
    by_cases exceptional : (rational.num.natAbs,rational.den) ∈ rationalExceptionalPairs
    · exact .exceptionalRational rational.num.natAbs rational.den rational.reduced exceptional representation
    · exact .finiteLowDenominator rational.num.natAbs rational.den rational.reduced denominator_lower denominator_upper
        numerator_lower numerator_upper exceptional representation
  · exact .largeExponent rational.num.natAbs rational.den rational.reduced denominator_lower denominator_upper
      (by rw [← representation]; exact le_of_not_gt bounded) representation

end LambdaCantor.RealPowers
