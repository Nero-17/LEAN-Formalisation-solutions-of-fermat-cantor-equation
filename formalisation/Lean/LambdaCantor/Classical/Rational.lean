import LambdaCantor.Classical.PeriodicArithmetic
import Mathlib.Data.Rat.Lemmas

noncomputable section
namespace LambdaCantor.Classical

theorem integer_circle_three_divides {first second denominator : ℤ}
    (equation : first ^ 2 + second ^ 2 = denominator ^ 2)
    (denominator_mod : denominator % 3 = 0) : first % 3 = 0 ∧ second % 3 = 0 := by
  have first_lower := Int.emod_nonneg first (by norm_num : (3 : ℤ) ≠ 0)
  have second_lower := Int.emod_nonneg second (by norm_num : (3 : ℤ) ≠ 0)
  have first_upper := Int.emod_lt_of_pos first (by norm_num : (0 : ℤ) < 3)
  have second_upper := Int.emod_lt_of_pos second (by norm_num : (0 : ℤ) < 3)
  have residues := congrArg (fun number : ℤ => number % 3) equation
  simp only [pow_two, Int.add_emod, Int.mul_emod, Int.emod_emod, denominator_mod] at residues
  simp only [Int.emod_emod] at residues
  interval_cases hfirst : first % 3 <;> interval_cases hsecond : second % 3 <;>
    norm_num at *

theorem rational_common_denominator (first second : ℚ) :
    ∃ denominator : ℕ, 0 < denominator ∧ ∃ firstNumerator secondNumerator : ℤ,
      (first : ℝ) * denominator = firstNumerator ∧
      (second : ℝ) * denominator = secondNumerator := by
  have first_denominator : (first.den : ℝ) ≠ 0 := by exact_mod_cast first.den_nz
  have second_denominator : (second.den : ℝ) ≠ 0 := by exact_mod_cast second.den_nz
  refine ⟨first.den * second.den, Nat.mul_pos first.den_pos second.den_pos,
    first.num * second.den, second.num * first.den, ?_, ?_⟩
  · rw [Rat.cast_def]
    push_cast
    field_simp
  · rw [Rat.cast_def]
    push_cast
    field_simp

/-- Minimal common denominators of rational unit-circle points are coprime to three. -/
theorem rational_circle_common_coprime (first second : ℚ)
    (circle : (first : ℝ) ^ 2 + (second : ℝ) ^ 2 = 1) :
    ∃ denominator : ℕ, 0 < denominator ∧ Nat.Coprime denominator 3 ∧
      ∃ firstNumerator secondNumerator : ℤ,
        (first : ℝ) * denominator = firstNumerator ∧
        (second : ℝ) * denominator = secondNumerator := by
  classical
  let denominator := Nat.find (rational_common_denominator first second)
  obtain ⟨positive, firstNumerator, secondNumerator, first_equation, second_equation⟩ :=
    Nat.find_spec (rational_common_denominator first second)
  change 0 < denominator at positive
  change (first : ℝ) * denominator = firstNumerator at first_equation
  change (second : ℝ) * denominator = secondNumerator at second_equation
  have not_divisible : ¬ 3 ∣ denominator := by
    intro divisible
    have denominator_mod : denominator % 3 = 0 := Nat.mod_eq_zero_of_dvd divisible
    have real_equation : (firstNumerator : ℝ) ^ 2 + (secondNumerator : ℝ) ^ 2 =
        (denominator : ℝ) ^ 2 := by
      rw [← first_equation, ← second_equation]
      nlinarith [congrArg (fun value : ℝ => (denominator : ℝ) ^ 2 * value) circle]
    have integer_equation : firstNumerator ^ 2 + secondNumerator ^ 2 =
        (denominator : ℤ) ^ 2 := by exact_mod_cast real_equation
    have denominator_integer_mod : (denominator : ℤ) % 3 = 0 := by
      exact_mod_cast denominator_mod
    obtain ⟨first_mod, second_mod⟩ :=
      integer_circle_three_divides integer_equation denominator_integer_mod
    have first_decomposition : firstNumerator = 3 * (firstNumerator / 3) := by omega
    have second_decomposition : secondNumerator = 3 * (secondNumerator / 3) := by omega
    have denominator_decomposition : denominator = 3 * (denominator / 3) := by omega
    have smaller : denominator / 3 < denominator := by omega
    apply Nat.find_min (rational_common_denominator first second) smaller
    refine ⟨by omega, firstNumerator / 3, secondNumerator / 3, ?_, ?_⟩
    · have first_real : (firstNumerator : ℝ) = 3 * ((firstNumerator / 3 : ℤ) : ℝ) := by
        exact_mod_cast first_decomposition
      have denominator_real : (denominator : ℝ) = 3 * (denominator / 3 : ℕ) := by
        exact_mod_cast denominator_decomposition
      rw [denominator_real, first_real] at first_equation
      nlinarith
    · have second_real : (secondNumerator : ℝ) = 3 * ((secondNumerator / 3 : ℤ) : ℝ) := by
        exact_mod_cast second_decomposition
      have denominator_real : (denominator : ℝ) = 3 * (denominator / 3 : ℕ) := by
        exact_mod_cast denominator_decomposition
      rw [denominator_real, second_real] at second_equation
      nlinarith
  refine ⟨denominator, positive, ?_, firstNumerator, secondNumerator,
    first_equation, second_equation⟩
  exact ((Nat.prime_three.coprime_iff_not_dvd).mpr not_divisible).symm

theorem reduced_denominator_dvd (rational : ℚ) (denominator : ℕ) (numerator : ℤ)
    (positive : 0 < denominator)
    (equation : (rational : ℝ) * denominator = numerator) :
    rational.den ∣ denominator := by
  have equation_rat : rational * (denominator : ℚ) = (numerator : ℚ) := by
    exact_mod_cast equation
  have representation : rational = Rat.divInt numerator (denominator : ℤ) := by
    rw [Rat.divInt_eq_div, Int.cast_natCast]
    exact (eq_div_iff (by exact_mod_cast (ne_of_gt positive))).mpr equation_rat
  have divides := Rat.den_dvd numerator (denominator : ℤ)
  rw [← representation] at divides
  exact_mod_cast divides

theorem rational_circle_denominators_coprime (first second : ℚ)
    (circle : (first : ℝ) ^ 2 + (second : ℝ) ^ 2 = 1) :
    Nat.Coprime first.den 3 ∧ Nat.Coprime second.den 3 := by
  obtain ⟨denominator, positive, coprime, firstNumerator, secondNumerator,
    first_equation, second_equation⟩ := rational_circle_common_coprime first second circle
  exact ⟨coprime.of_dvd_left (reduced_denominator_dvd first denominator firstNumerator
      positive first_equation),
    coprime.of_dvd_left (reduced_denominator_dvd second denominator secondNumerator
      positive second_equation)⟩

theorem no_rational_interior_circle (first second : ℚ)
    (first_positive : 0 < first) (first_less_one : first < 1)
    (second_positive : 0 < second) (second_less_one : second < 1)
    (first_member : (first : ℝ) ∈ cantorSet (1 / 3))
    (second_member : (second : ℝ) ∈ cantorSet (1 / 3))
    (circle : (first : ℝ) ^ 2 + (second : ℝ) ^ 2 = 1) : False := by
  obtain ⟨first_digits, first_represents⟩ := first_member
  obtain ⟨second_digits, second_represents⟩ := second_member
  have coprime := rational_circle_denominators_coprime first second circle
  obtain ⟨firstPeriod, first_period_positive, first_periodic⟩ :=
    rational_address_pure_periodic first first_positive first_less_one coprime.1
      first_digits first_represents
  obtain ⟨secondPeriod, second_period_positive, second_periodic⟩ :=
    rational_address_pure_periodic second second_positive second_less_one coprime.2
      second_digits second_represents
  have axes := periodic_circle_axes first_digits second_digits firstPeriod secondPeriod
    first_period_positive second_period_positive first_periodic second_periodic
    (by rwa [first_represents, second_represents])
  rw [first_represents, second_represents] at axes
  have first_real_positive : (0 : ℝ) < first := by exact_mod_cast first_positive
  have second_real_positive : (0 : ℝ) < second := by exact_mod_cast second_positive
  rcases axes with first_axis | second_axis <;> linarith

/-- Exactly the two axis points remain among rational Cantor-circle points. -/
theorem rational_circle_axes (first second : ℚ)
    (first_member : (first : ℝ) ∈ cantorSet (1 / 3))
    (second_member : (second : ℝ) ∈ cantorSet (1 / 3))
    (circle : (first : ℝ) ^ 2 + (second : ℝ) ^ 2 = 1) :
    (first = 0 ∧ second = 1) ∨ (first = 1 ∧ second = 0) := by
  have first_bounds := LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) first_member
  have second_bounds := LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) second_member
  by_cases first_zero : first = 0
  · left
    refine ⟨first_zero, ?_⟩
    have second_one : (second : ℝ) = 1 := by
      norm_num [first_zero] at circle
      rcases circle with circle | circle <;> linarith [second_bounds.1]
    exact_mod_cast second_one
  by_cases second_zero : second = 0
  · right
    refine ⟨?_, second_zero⟩
    have first_one : (first : ℝ) = 1 := by
      norm_num [second_zero] at circle
      rcases circle with circle | circle <;> linarith [first_bounds.1]
    exact_mod_cast first_one
  have first_nonzero : (first : ℝ) ≠ 0 := by exact_mod_cast first_zero
  have second_nonzero : (second : ℝ) ≠ 0 := by exact_mod_cast second_zero
  have first_positive : (0 : ℝ) < first := by rcases first_bounds with ⟨_, _⟩; positivity
  have second_positive : (0 : ℝ) < second := by rcases second_bounds with ⟨_, _⟩; positivity
  have first_less_one : (first : ℝ) < 1 := by nlinarith [sq_pos_of_pos second_positive]
  have second_less_one : (second : ℝ) < 1 := by nlinarith [sq_pos_of_pos first_positive]
  exact False.elim (no_rational_interior_circle first second
    (by exact_mod_cast first_positive) (by exact_mod_cast first_less_one)
    (by exact_mod_cast second_positive) (by exact_mod_cast second_less_one)
    first_member second_member circle)

end LambdaCantor.Classical
