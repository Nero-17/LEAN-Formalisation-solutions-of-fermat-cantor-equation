import LambdaCantor.Last.ArithmeticDigitTheorem
import LambdaCantor.Last.AnalyticIsolatedPeriodic
import Mathlib.RingTheory.Algebraic.Integral

noncomputable section
namespace LambdaCantor.Last

def booleanIntegerDigits (digits : ℕ → Bool) (index : ℕ) : ℤ :=
  if digits index then 1 else 0

theorem address_eq_integerDigitSeries (ratio : ℝ) (digits : ℕ → Bool) :
    address ratio digits = (1-ratio)*integerDigitSeries ratio⁻¹ (booleanIntegerDigits digits) := by
  unfold address integerDigitSeries
  congr 1
  apply tsum_congr
  intro index
  cases digit : digits index <;> simp [booleanIntegerDigits, digit, div_eq_mul_inv, inv_pow]

theorem critical_ratio_inverse {ratio : ℝ} (critical : ratio = (Real.sqrt 3-1)/2) :
    ratio⁻¹ = 1+Real.sqrt 3 := by
  rw [critical]
  apply inv_eq_of_mul_eq_one_left
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

theorem critical_ratio_algebraic {ratio : ℝ} (critical : ratio = (Real.sqrt 3-1)/2) :
    IsAlgebraic ℚ ratio := by
  refine ⟨Polynomial.X^2+Polynomial.X-Polynomial.C (1/2 : ℚ), ?_, ?_⟩
  · exact (show (Polynomial.X^2+Polynomial.X-Polynomial.C (1/2 : ℚ)).Monic by
      monicity <;> norm_num).ne_zero
  · simp
    rw [critical]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

/-- The arithmetic boundary step is fully explicit: long alternating blocks
give the stammering condition internally, and algebraicity excludes the
transcendental alternative in the general digit theorem. The still-needed
geometric input is exactly the displayed block condition. -/
theorem boundary_algebraic_address_mem_parameterField {ratio : ℝ}
    (critical : ratio = (Real.sqrt 3-1)/2) (digits : ℕ → Bool)
    (algebraic_address : IsAlgebraic ℚ (address ratio digits))
    (fixedLoss : ℕ)
    (blocks : ∀ threshold : ℕ, ∃ start : ℕ, threshold ≤ start ∧
      IntegerAlternatingBlock (booleanIntegerDigits digits) start (start-fixedLoss)) :
    address ratio digits ∈ parameterField ratio := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have ratio_positive : 0 < ratio := by rw [critical]; nlinarith
  have ratio_less_one : ratio < 1 := by rw [critical]; nlinarith
  by_cases periodic : EventuallyPeriodicIntegerSequence (booleanIntegerDigits digits)
  · obtain ⟨prefixLength, period, period_positive, periodic⟩ := periodic
    apply eventually_periodic_address_mem_parameterField ratio_positive.le ratio_less_one
      digits prefixLength period period_positive
    intro index
    have equal := periodic index
    cases first : digits (index+prefixLength+period) <;> cases second : digits (index+prefixLength) <;>
      simp_all [booleanIntegerDigits]
  · have stammering := doubleStammering_of_long_alternating_blocks
      (booleanIntegerDigits digits) periodic fixedLoss blocks
    have bounded : ∃ bound : ℕ, ∀ index, |booleanIntegerDigits digits index| ≤ (bound : ℤ) := by
      refine ⟨1, ?_⟩
      intro index
      cases digit : digits index <;> simp [booleanIntegerDigits, digit]
    have pisot : PisotSeriesBase ratio⁻¹ := by
      rw [critical_ratio_inverse critical]
      exact quadratic_boundary_pisot
    have series_eq : integerDigitSeries ratio⁻¹ (booleanIntegerDigits digits) =
        address ratio digits/(1-ratio) := by
      apply (eq_div_iff (show 1-ratio ≠ 0 by linarith)).mpr
      rw [address_eq_integerDigitSeries]
      ring
    have algebraic_series : IsAlgebraic ℚ
        (integerDigitSeries ratio⁻¹ (booleanIntegerDigits digits)) := by
      rw [series_eq, div_eq_mul_inv]
      exact algebraic_address.mul ((isAlgebraic_one.sub (critical_ratio_algebraic critical)).inv)
    rcases External.adamczewski_bugeaud_pisot_stammering ratio⁻¹ pisot
      (booleanIntegerDigits digits) bounded stammering with in_field | transcendental
    · have series_in_field : integerDigitSeries ratio⁻¹ (booleanIntegerDigits digits) ∈
          parameterField ratio := by
        rw [← parameterField_inv_eq ratio]
        exact in_field
      rw [address_eq_integerDigitSeries]
      exact (parameterField ratio).mul_mem
        ((parameterField ratio).sub_mem (parameterField ratio).one_mem
          (ratio_mem_parameterField ratio)) series_in_field
    · exact (transcendental algebraic_series).elim

end LambdaCantor.Last
