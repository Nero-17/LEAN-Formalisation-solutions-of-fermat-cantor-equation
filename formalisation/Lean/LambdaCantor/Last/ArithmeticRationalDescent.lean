import LambdaCantor.Last.ArithmeticRationalRootCore
import LambdaCantor.Last.ArithmeticRadicalDescent

noncomputable section
namespace LambdaCantor.Last
/-- Raising a positive reduced rational power to its denominator recovers
the integer numerator power, with real-power semantics made explicit. -/
theorem rational_power_pow_denominator {coordinate : ℝ} (positive : 0 < coordinate)
    (numerator : ℕ) {denominator : ℕ} (denominator_positive : 0 < denominator) :
    (coordinate ^ ((numerator : ℝ)/denominator)) ^ denominator = coordinate ^ numerator := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul positive.le,
    div_mul_cancel₀ _ (show (denominator : ℝ) ≠ 0 by exact_mod_cast denominator_positive.ne'),
    Real.rpow_natCast]

/-- Generic positive rational-radix descent for reuse outside the Cantor
project: no hypothesis concerns λ, addresses, or a special ground field. -/
theorem positive_rational_fermat_roots_mem_subfield
    (field : Subfield ℝ) {first second : ℝ}
    (first_positive : 0 < first) (second_positive : 0 < second)
    {numerator denominator : ℕ} (denominator_positive : 0 < denominator)
    (coprime : numerator.Coprime denominator)
    (first_mem : first ∈ field) (second_mem : second ∈ field)
    (equation : first ^ ((numerator : ℝ)/denominator) +
      second ^ ((numerator : ℝ)/denominator) = 1) :
    first ^ (1/(denominator : ℝ)) ∈ field ∧
      second ^ (1/(denominator : ℝ)) ∈ field := by
  have first_power_mem : (first ^ ((numerator : ℝ)/denominator)) ^ denominator ∈ field := by
    rw [rational_power_pow_denominator first_positive numerator denominator_positive]
    exact field.pow_mem first_mem numerator
  have second_power_mem : (second ^ ((numerator : ℝ)/denominator)) ^ denominator ∈ field := by
    rw [rational_power_pow_denominator second_positive numerator denominator_positive]
    exact field.pow_mem second_mem numerator
  have rational_powers_mem := positive_radicals_mem_subfield field
    (Real.rpow_pos_of_pos first_positive _) (Real.rpow_pos_of_pos second_positive _)
    equation denominator_positive first_power_mem second_power_mem
  exact ⟨denominator_root_mem_subfield field first_positive denominator_positive coprime
      first_mem rational_powers_mem.1,
    denominator_root_mem_subfield field second_positive denominator_positive coprime
      second_mem rational_powers_mem.2⟩


end LambdaCantor.Last

