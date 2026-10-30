import LambdaCantor.Last.ArithmeticStammering
import LambdaCantor.Last.ArithmeticField
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.ComputeDegree

/-!
External theorem registration: Adamczewski–Bugeaud, Annals of Mathematics
165 (2007), Theorem 5, pp.553–554. Primary author PDF:
https://adamczewski.perso.math.cnrs.fr/ComplexityI.pdf

The theorem applies to arbitrary bounded rational-integer sequences and any
Pisot or Salem base. We register the Pisot case and the exact-double special
case of Condition (*)w with w=2. `DoubleStammering` spells out nonperiodicity,
strictly increasing repeated-word lengths, bounded prefixLength/word ratios, and
two consecutive identical words; no geometric or Cantor conclusion occurs.

Indexing here begins at zero. Multiplying the paper's one-indexed series by
the algebraic nonzero base gives this equivalent statement: both membership
in Q(base) and algebraicity/transcendence are preserved by that multiplication.
-/

noncomputable section
namespace LambdaCantor.Last

/-- Conventional Pisot definition: a real algebraic integer above one, all
of whose other complex conjugates lie strictly inside the unit circle. -/
def PisotSeriesBase (base : ℝ) : Prop :=
  1 < base ∧ IsIntegral ℤ base ∧
    ∀ conjugate ∈ (minpoly ℚ base).rootSet ℂ,
      conjugate ≠ (base : ℂ) → ‖conjugate‖ < 1

def integerDigitSeries (base : ℝ) (digits : ℕ → ℤ) : ℝ :=
  ∑' index : ℕ, (digits index : ℝ)/base^index

namespace External

/-- Theorem 5 of Adamczewski–Bugeaud in its general Pisot/double-word case.
This is an explicitly registered established external theorem. -/
axiom adamczewski_bugeaud_pisot_stammering
    (base : ℝ) (pisot : PisotSeriesBase base) (digits : ℕ → ℤ)
    (bounded : ∃ bound : ℕ, ∀ index, |digits index| ≤ (bound : ℤ))
    (stammering : DoubleStammering digits) :
    integerDigitSeries base digits ∈ parameterField base ∨
      Transcendental ℚ (integerDigitSeries base digits)

end External

theorem parameterField_inv_eq (value : ℝ) : parameterField value⁻¹ = parameterField value := by
  apply le_antisymm
  · exact parameterField_le ((parameterField value).inv_mem (ratio_mem_parameterField value))
  · apply parameterField_le
    simpa using (parameterField value⁻¹).inv_mem (ratio_mem_parameterField value⁻¹)

theorem quadratic_boundary_pisot : PisotSeriesBase (1+Real.sqrt 3) := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have sqrt_gt_one : 1 < Real.sqrt 3 := by nlinarith
  have sqrt_lt_two : Real.sqrt 3 < 2 := by nlinarith
  have integer_integral : IsIntegral ℤ (1+Real.sqrt 3) := by
    refine ⟨Polynomial.X^2-Polynomial.C 2*Polynomial.X-Polynomial.C 2, ?_, ?_⟩
    · monicity <;> norm_num
    · norm_num [Polynomial.aeval_C] <;> nlinarith
  refine ⟨by linarith, integer_integral, ?_⟩
  intro conjugate membership different
  have annihilates : Polynomial.aeval (1+Real.sqrt 3)
      (Polynomial.X^2-Polynomial.C 2*Polynomial.X-Polynomial.C 2 : Polynomial ℚ) = 0 := by
    norm_num [Polynomial.aeval_C] <;> nlinarith
  obtain ⟨factor, factorization⟩ := minpoly.dvd ℚ (1+Real.sqrt 3) annihilates
  have minimal_zero := Polynomial.aeval_eq_zero_of_mem_rootSet membership
  have quadratic_zero : conjugate^2-2*conjugate-2=0 := by
    have evaluation : Polynomial.aeval conjugate
        (Polynomial.X^2-Polynomial.C 2*Polynomial.X-Polynomial.C 2 : Polynomial ℚ) = 0 := by
      rw [factorization, map_mul, minimal_zero, zero_mul]
    simpa [Polynomial.aeval_C] using evaluation
  have sqrt_complex_square : (Real.sqrt 3 : ℂ)^2 = 3 := by exact_mod_cast sqrt_square
  have factorized : (conjugate-(1+Real.sqrt 3))*(conjugate-(1-Real.sqrt 3))=0 := by
    calc
      _ = (conjugate^2-2*conjugate-2) - ((Real.sqrt 3 : ℂ)^2-3) := by ring
      _ = 0 := by rw [quadratic_zero, sqrt_complex_square]; ring
  have conjugate_eq : conjugate = (1-Real.sqrt 3 : ℝ) := by
    rcases mul_eq_zero.mp factorized with first | second
    · exact (different (by simpa using sub_eq_zero.mp first)).elim
    · simpa only [Complex.ofReal_sub, Complex.ofReal_one] using sub_eq_zero.mp second
  rw [conjugate_eq, Complex.norm_real, Real.norm_eq_abs]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end LambdaCantor.Last
