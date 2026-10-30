import LambdaCantor.Last.ArithmeticRationalDescent
import Mathlib.RingTheory.Algebraic.Integral

noncomputable section
namespace LambdaCantor.Last

theorem isAlgebraic_rational_rpow {coordinate : ℝ} (positive : 0 < coordinate)
    (algebraic : IsAlgebraic ℚ coordinate) (numerator : ℕ)
    {denominator : ℕ} (denominator_positive : 0 < denominator) :
    IsAlgebraic ℚ (coordinate ^ ((numerator : ℝ)/denominator)) := by
  apply IsAlgebraic.of_pow denominator_positive
  rw [rational_power_pow_denominator positive numerator denominator_positive]
  exact algebraic.pow numerator

theorem isAlgebraic_of_rational_rpow {coordinate : ℝ} (positive : 0 < coordinate)
    {numerator denominator : ℕ} (numerator_positive : 0 < numerator)
    (denominator_positive : 0 < denominator)
    (power_algebraic : IsAlgebraic ℚ (coordinate ^ ((numerator : ℝ)/denominator))) :
    IsAlgebraic ℚ coordinate := by
  apply IsAlgebraic.of_pow numerator_positive
  rw [← rational_power_pow_denominator positive numerator denominator_positive]
  exact power_algebraic.pow denominator

theorem positive_rational_fermat_algebraic_of_quotient
    {first second : ℝ} (first_positive : 0 < first) (second_positive : 0 < second)
    {numerator denominator : ℕ} (numerator_positive : 0 < numerator)
    (denominator_positive : 0 < denominator)
    (equation : first ^ ((numerator : ℝ)/denominator)+
      second ^ ((numerator : ℝ)/denominator)=1)
    (quotient_algebraic : IsAlgebraic ℚ (second/first)) :
    IsAlgebraic ℚ first ∧ IsAlgebraic ℚ second := by
  have quotient_positive := div_pos second_positive first_positive
  have quotient_power_algebraic := isAlgebraic_rational_rpow quotient_positive
    quotient_algebraic numerator denominator_positive
  have first_power_positive := Real.rpow_pos_of_pos first_positive ((numerator : ℝ)/denominator)
  have quotient_power_positive := Real.rpow_pos_of_pos quotient_positive ((numerator : ℝ)/denominator)
  have quotient_power_relation : (second/first)^((numerator : ℝ)/denominator)*
      first^((numerator : ℝ)/denominator) = second^((numerator : ℝ)/denominator) := by
    rw [Real.div_rpow second_positive.le first_positive.le, div_mul_cancel₀ _ first_power_positive.ne']
  have first_power_eq : first^((numerator : ℝ)/denominator) =
      1/(1+(second/first)^((numerator : ℝ)/denominator)) := by
    apply (eq_div_iff (show 1+(second/first)^((numerator : ℝ)/denominator) ≠ 0 by positivity)).mpr
    nlinarith
  have first_power_algebraic : IsAlgebraic ℚ (first^((numerator : ℝ)/denominator)) := by
    rw [first_power_eq, one_div]
    exact (isAlgebraic_one.add quotient_power_algebraic).inv
  have first_algebraic := isAlgebraic_of_rational_rpow first_positive
    numerator_positive denominator_positive first_power_algebraic
  refine ⟨first_algebraic, ?_⟩
  simpa [div_mul_cancel₀ _ first_positive.ne'] using quotient_algebraic.mul first_algebraic

/-- At the critical tangent phases, rationality of the exponent and an
algebraic tangent force both actual positive Fermat coordinates algebraic.
No digit theorem or isolated-point assumption is used in this step. -/
theorem positive_rational_fermat_algebraic_of_tangent
    {first second : ℝ} (first_positive : 0 < first) (second_positive : 0 < second)
    {numerator denominator : ℕ} (denominator_positive : 0 < denominator)
    (exponent_gt_one : denominator < numerator)
    (equation : first ^ ((numerator : ℝ)/denominator)+
      second ^ ((numerator : ℝ)/denominator)=1)
    (tangent_algebraic : IsAlgebraic ℚ ((second/first)^((numerator : ℝ)/denominator-1))) :
    IsAlgebraic ℚ first ∧ IsAlgebraic ℚ second := by
  have quotient_positive := div_pos second_positive first_positive
  have reduced_exponent : (numerator : ℝ)/denominator-1 =
      ((numerator-denominator : ℕ) : ℝ)/denominator := by
    rw [Nat.cast_sub exponent_gt_one.le]
    field_simp [show (denominator : ℝ) ≠ 0 by exact_mod_cast denominator_positive.ne']
  rw [reduced_exponent] at tangent_algebraic
  have quotient_algebraic := isAlgebraic_of_rational_rpow quotient_positive
    (Nat.sub_pos_of_lt exponent_gt_one) denominator_positive tangent_algebraic
  exact positive_rational_fermat_algebraic_of_quotient first_positive second_positive
    (by omega) denominator_positive equation quotient_algebraic

end LambdaCantor.Last
