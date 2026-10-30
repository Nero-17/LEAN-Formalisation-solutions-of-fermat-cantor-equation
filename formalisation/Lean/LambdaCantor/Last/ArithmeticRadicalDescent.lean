import LambdaCantor.Last.ArithmeticField
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor.Last

/-- The equality case of the triangle inequality, written as two circle
equations. Positive radii summing to one force their unique contact point. -/
theorem complex_eq_real_of_norms {first second : ℝ} (sum_one : first+second=1)
    {value : ℂ} (first_norm : ‖value‖ = first) (second_norm : ‖1-value‖ = second) :
    value = (first : ℂ) := by
  have first_square := Complex.sq_norm value
  have second_square := Complex.sq_norm (1-value)
  simp only [first_norm, second_norm, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at first_square second_square
  have second_eq : second = 1-first := by linarith
  rw [second_eq] at second_square
  have real_part : value.re = first := by nlinarith
  rw [real_part] at first_square
  have imaginary_part : value.im = 0 := by nlinarith [sq_nonneg value.im]
  apply Complex.ext
  · simpa using real_part
  · simpa using imaginary_part

theorem complex_positive_radical_unique {first second : ℝ}
    (first_positive : 0 < first) (second_positive : 0 < second) (sum_one : first+second=1)
    {degree : ℕ} (degree_positive : 0 < degree) {value : ℂ}
    (first_power : value ^ degree = (first : ℂ) ^ degree)
    (second_power : (1-value) ^ degree = (second : ℂ) ^ degree) :
    value = (first : ℂ) := by
  apply complex_eq_real_of_norms sum_one
  · apply (pow_left_inj₀ (norm_nonneg value) first_positive.le degree_positive.ne').mp
    simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos first_positive]
      using congrArg norm first_power
  · apply (pow_left_inj₀ (norm_nonneg (1-value)) second_positive.le degree_positive.ne').mp
    simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos second_positive]
      using congrArg norm second_power

/-- Positive radicals adding to one descend to their real ground field.
The proof uses the actual minimal polynomial and all its complex roots:
each root lies on the same two tangent circles, hence all conjugates coincide;
characteristic-zero separability then forces the minimal polynomial to have
degree one. No external radical-descent assertion is used. -/
theorem positive_radicals_mem_subfield (field : Subfield ℝ)
    {first second : ℝ} (first_positive : 0 < first) (second_positive : 0 < second)
    (sum_one : first+second=1) {degree : ℕ} (degree_positive : 0 < degree)
    (first_power_mem : first ^ degree ∈ field) (second_power_mem : second ^ degree ∈ field) :
    first ∈ field ∧ second ∈ field := by
  classical
  letI : Algebra field ℂ := (Complex.ofRealHom.comp field.subtype).toAlgebra
  have first_integral : IsIntegral field first := by
    apply IsIntegral.of_pow degree_positive
    change IsIntegral field (algebraMap field ℝ ⟨first ^ degree, first_power_mem⟩)
    exact isIntegral_algebraMap
  have minimal_nonzero := minpoly.ne_zero first_integral
  have first_annihilates : Polynomial.aeval first
      (Polynomial.X ^ degree - Polynomial.C (⟨first ^ degree, first_power_mem⟩ : field)) = 0 := by
    simp [Subfield.algebraMap_ofSubfield]
  have second_annihilates : Polynomial.aeval first
      ((1-Polynomial.X) ^ degree - Polynomial.C (⟨second ^ degree, second_power_mem⟩ : field)) = 0 := by
    have second_eq : 1-first = second := by linarith
    simp [second_eq, Subfield.algebraMap_ofSubfield]
  obtain ⟨first_factor, first_factorization⟩ := minpoly.dvd field first first_annihilates
  obtain ⟨second_factor, second_factorization⟩ := minpoly.dvd field first second_annihilates
  have roots_unique : ∀ root ∈ (minpoly field first).rootSet ℂ, root = (first : ℂ) := by
    intro root membership
    have root_zero : Polynomial.aeval root (minpoly field first) = 0 :=
      Polynomial.aeval_eq_zero_of_mem_rootSet membership
    have first_equation : Polynomial.aeval root
        (Polynomial.X ^ degree - Polynomial.C (⟨first ^ degree, first_power_mem⟩ : field)) = 0 := by
      rw [first_factorization, map_mul, root_zero, zero_mul]
    have second_equation : Polynomial.aeval root
        ((1-Polynomial.X) ^ degree - Polynomial.C (⟨second ^ degree, second_power_mem⟩ : field)) = 0 := by
      rw [second_factorization, map_mul, root_zero, zero_mul]
    apply complex_positive_radical_unique first_positive second_positive sum_one degree_positive
    · simpa [RingHom.algebraMap_toAlgebra, sub_eq_zero] using first_equation
    · simpa [RingHom.algebraMap_toAlgebra, sub_eq_zero] using second_equation
  have roots_subsingleton : Subsingleton ((minpoly field first).rootSet ℂ) := by
    constructor
    intro left right
    apply Subtype.ext
    exact (roots_unique left left.property).trans (roots_unique right right.property).symm
  letI := roots_subsingleton
  have roots_card_le : Fintype.card ((minpoly field first).rootSet ℂ) ≤ 1 :=
    Fintype.card_le_one_iff_subsingleton.mpr roots_subsingleton
  have degree_le_one : (minpoly field first).natDegree ≤ 1 := by
    rwa [Polynomial.card_rootSet_eq_natDegree
      (minpoly.irreducible first_integral).separable (IsAlgClosed.splits _)] at roots_card_le
  have degree_one : (minpoly field first).natDegree = 1 := by
    have positive_degree := minpoly.natDegree_pos first_integral
    omega
  obtain ⟨field_value, field_value_eq⟩ := minpoly.natDegree_eq_one_iff.mp degree_one
  have first_mem : first ∈ field := by
    rw [← field_value_eq]
    exact field_value.property
  refine ⟨first_mem, ?_⟩
  have second_eq : second = 1-first := by linarith
  rw [second_eq]
  exact field.sub_mem field.one_mem first_mem

end LambdaCantor.Last
