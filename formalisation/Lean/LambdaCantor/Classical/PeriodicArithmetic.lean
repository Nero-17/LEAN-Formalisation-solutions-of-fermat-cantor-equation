import LambdaCantor.Classical.Arithmetic
import LambdaCantor.Addresses
import LambdaCantor.ClassicalBridge
import LambdaCantor.External.Positional

noncomputable section
namespace LambdaCantor.Classical

def wordValue (digits : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | length + 1 => 3 * wordValue digits length + if digits length then 1 else 0

theorem wordValue_word (digits : ℕ → Bool) (length : ℕ) :
    ZeroOneWord length (wordValue digits length) := by
  induction length with
  | zero => exact .nil
  | succ length inductionHypothesis =>
    cases digit : digits length
    · simpa [wordValue, digit] using ZeroOneWord.zero inductionHypothesis
    · simpa [wordValue, digit] using ZeroOneWord.one inductionHypothesis

theorem prefixValue_wordValue (digits : ℕ → Bool) (length : ℕ) :
    prefixValue (1 / 3) digits length =
      2 * (wordValue digits length : ℝ) / 3 ^ length := by
  induction length with
  | zero => simp [prefixValue, wordValue]
  | succ length inductionHypothesis =>
    have prefix_successor : prefixValue (1 / 3) digits (length + 1) =
        prefixValue (1 / 3) digits length +
          (2 / 3 : ℝ) * (if digits length then 1 else 0) * (1 / 3) ^ length := by
      simp only [prefixValue, Finset.sum_range_succ]
      ring
    rw [prefix_successor, inductionHypothesis, wordValue]
    push_cast
    cases digit : digits length <;> simp [digit, pow_succ, div_pow] <;> ring

theorem periodic_multiple (digits : ℕ → Bool) (period : ℕ)
    (periodic : ∀ n, digits (n + period) = digits n) (multiple : ℕ) :
    ∀ n, digits (n + period * multiple) = digits n := by
  induction multiple with
  | zero => simp
  | succ multiple inductionHypothesis =>
    intro n
    rw [Nat.mul_succ, ← Nat.add_assoc, periodic, inductionHypothesis]

theorem periodic_address_repunit (digits : ℕ → Bool) (period : ℕ)
    (periodic : ∀ n, digits (n + period) = digits n) :
    (repunit period : ℝ) * address (1 / 3) digits = wordValue digits period := by
  have split := address_prefix_tail (ratio := (1 / 3 : ℝ)) (by norm_num)
    (by norm_num) digits period
  have tail : (fun j => digits (j + period)) = digits := funext periodic
  rw [tail, prefixValue_wordValue] at split
  have power_positive : 0 < (3 : ℝ) ^ period := by positivity
  have repunit_real : 2 * (repunit period : ℝ) + 1 = (3 : ℝ) ^ period := by
    exact_mod_cast repunit_formula period
  have cleared := congrArg (fun value : ℝ => value * 3 ^ period) split
  simp only [div_pow, one_pow] at cleared
  field_simp at cleared
  have repunit_scaled := congrArg (fun value : ℝ => value * address (1 / 3) digits) repunit_real
  nlinarith [repunit_scaled]

/-- The circle obstruction for any two purely periodic zero-two addresses. -/
theorem periodic_circle_axes (first second : ℕ → Bool) (firstPeriod secondPeriod : ℕ)
    (first_positive : 0 < firstPeriod) (second_positive : 0 < secondPeriod)
    (first_periodic : ∀ n, first (n + firstPeriod) = first n)
    (second_periodic : ∀ n, second (n + secondPeriod) = second n)
    (circle : address (1 / 3) first ^ 2 + address (1 / 3) second ^ 2 = 1) :
    (address (1 / 3) first = 0 ∧ address (1 / 3) second = 1) ∨
      (address (1 / 3) first = 1 ∧ address (1 / 3) second = 0) := by
  have first_relation := periodic_address_repunit first (firstPeriod * secondPeriod)
    (periodic_multiple first firstPeriod first_periodic secondPeriod)
  have second_relation := periodic_address_repunit second (firstPeriod * secondPeriod)
    (by simpa [Nat.mul_comm] using
      periodic_multiple second secondPeriod second_periodic firstPeriod)
  have positive_length : 0 < firstPeriod * secondPeriod := Nat.mul_pos first_positive second_positive
  have positive_repunit : 0 < repunit (firstPeriod * secondPeriod) := by
    cases length : firstPeriod * secondPeriod with
    | zero => omega
    | succ length => simp [repunit]
  have real_equation : (wordValue first (firstPeriod * secondPeriod) : ℝ) ^ 2 +
      (wordValue second (firstPeriod * secondPeriod) : ℝ) ^ 2 =
        (repunit (firstPeriod * secondPeriod) : ℝ) ^ 2 := by
    rw [← first_relation, ← second_relation]
    nlinarith [congrArg (fun value : ℝ =>
      (repunit (firstPeriod * secondPeriod) : ℝ) ^ 2 * value) circle]
  have natural_equation : wordValue first (firstPeriod * secondPeriod) ^ 2 +
      wordValue second (firstPeriod * secondPeriod) ^ 2 =
        repunit (firstPeriod * secondPeriod) ^ 2 := by exact_mod_cast real_equation
  have positive_real : (0 : ℝ) < repunit (firstPeriod * secondPeriod) := by
    exact_mod_cast positive_repunit
  rcases zeroOneWord_circle_axes (wordValue_word first _) (wordValue_word second _)
    natural_equation with first_axis | second_axis
  · left
    simp only [first_axis.1, first_axis.2, Nat.cast_zero] at first_relation second_relation
    constructor <;> nlinarith
  · right
    simp only [second_axis.1, second_axis.2, Nat.cast_zero] at first_relation second_relation
    constructor <;> nlinarith

theorem rational_address_pure_periodic (rational : ℚ)
    (positive : 0 < rational) (less_one : rational < 1)
    (coprime : Nat.Coprime rational.den 3) (digits : ℕ → Bool)
    (represents : address (1 / 3) digits = (rational : ℝ)) :
    ∃ period : ℕ, 0 < period ∧ ∀ n, digits (n + period) = digits n := by
  obtain ⟨period, period_positive, periodic⟩ :=
    External.periodic_digits_of_coprime_denominator (by norm_num : 2 ≤ 3)
      rational positive less_one coprime (fun n => cond (digits n) (2 : Fin 3) 0)
      (by rw [← address_third_eq_ofDigits]; exact represents)
  refine ⟨period, period_positive, fun n => ?_⟩
  have digit_equality := periodic n
  cases first : digits (n + period) <;> cases second : digits n <;>
    simp_all

end LambdaCantor.Classical
