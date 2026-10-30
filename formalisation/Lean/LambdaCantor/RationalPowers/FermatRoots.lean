import LambdaCantor.Integer.ExternalFermat
import LambdaCantor.Last.ArithmeticRationalDescent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace LambdaCantor.RationalPowers

/-- Once the established subfield descent supplies rational positive q-th
roots, the remaining rational-exponent obstruction is exactly integer FLT.
This adapter does not assume the descent statement or redeclare it as an axiom. -/
theorem no_positive_fermat_of_rational_roots (numerator denominator : ℕ)
    (numerator_ge_three : 3 ≤ numerator) (x y : ℝ) (x_positive : 0 < x) (y_positive : 0 < y)
    (first_root_rational : ∃ rational : ℚ, (rational : ℝ) = x^(1/(denominator : ℝ)))
    (second_root_rational : ∃ rational : ℚ, (rational : ℝ) = y^(1/(denominator : ℝ))) :
    x^((numerator : ℝ)/denominator)+y^((numerator : ℝ)/denominator) ≠ 1 := by
  have first_power : (x^(1/(denominator : ℝ)))^numerator =
      x^((numerator : ℝ)/denominator) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul x_positive.le]
    congr 1
    ring
  have second_power : (y^(1/(denominator : ℝ)))^numerator =
      y^((numerator : ℝ)/denominator) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul y_positive.le]
    congr 1
    ring
  have excluded := Integer.positive_rational_coordinates_not_on_fermat numerator numerator_ge_three
    (x^(1/(denominator : ℝ))) (y^(1/(denominator : ℝ)))
    (Real.rpow_pos_of_pos x_positive _) (Real.rpow_pos_of_pos y_positive _)
    first_root_rational second_root_rational
  simpa only [first_power, second_power] using excluded

theorem rational_exponent_numerator_ge_three (numerator denominator : ℕ)
    (denominator_positive : 0 < denominator)
    (exponent_gt_one : 1 < (numerator : ℝ)/denominator)
    (exponent_ne_two : (numerator : ℝ)/denominator ≠ 2) :
    3 ≤ numerator := by
  have denominator_real_positive : (0 : ℝ) < denominator := by exact_mod_cast denominator_positive
  have numerator_larger : denominator < numerator := by
    have cleared := (lt_div_iff₀ denominator_real_positive).mp exponent_gt_one
    have real_larger : (denominator : ℝ) < numerator := by simpa using cleared
    exact_mod_cast real_larger
  by_contra too_small
  have numerator_eq : numerator = 2 := by omega
  have denominator_eq : denominator = 1 := by omega
  subst numerator
  subst denominator
  norm_num at exponent_ne_two

/-- Every noncircle reduced rational exponent greater than one excludes
positive rational coordinate pairs. The root descent is the proved generic
subfield theorem, specialized to the actual rational-cast field. -/
theorem positive_rational_coordinates_not_on_real_fermat (numerator denominator : ℕ)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    (exponent_gt_one : 1 < (numerator : ℝ)/denominator)
    (exponent_ne_two : (numerator : ℝ)/denominator ≠ 2)
    (x y : ℝ) (x_positive : 0 < x) (y_positive : 0 < y)
    (first_rational : ∃ rational : ℚ, (rational : ℝ) = x)
    (second_rational : ∃ rational : ℚ, (rational : ℝ) = y) :
    x^((numerator : ℝ)/denominator)+y^((numerator : ℝ)/denominator) ≠ 1 := by
  intro equation
  have first_mem : x ∈ (Rat.castHom ℝ).fieldRange :=
    RingHom.mem_fieldRange.mpr first_rational
  have second_mem : y ∈ (Rat.castHom ℝ).fieldRange :=
    RingHom.mem_fieldRange.mpr second_rational
  have roots := Last.positive_rational_fermat_roots_mem_subfield (Rat.castHom ℝ).fieldRange
    x_positive y_positive denominator_positive coprime first_mem second_mem equation
  exact no_positive_fermat_of_rational_roots numerator denominator
    (rational_exponent_numerator_ge_three numerator denominator denominator_positive exponent_gt_one exponent_ne_two)
    x y x_positive y_positive (RingHom.mem_fieldRange.mp roots.1) (RingHom.mem_fieldRange.mp roots.2) equation

end LambdaCantor.RationalPowers

