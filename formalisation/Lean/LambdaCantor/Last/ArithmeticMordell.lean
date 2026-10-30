import LambdaCantor.Last.ArithmeticField
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases

/-!
External theorem registration, 2026-10-24.

The sole external statement below is the smooth projective plane-curve case
of Mordell's theorem over finitely generated characteristic-zero fields.
It applies to arbitrary homogeneous polynomials, not to the Cantor/Fermat
conclusion of the article. Its nonsingularity condition is checked over ℂ.
The finite affine chart follows by injecting it into the projective curve.

Primary source: Moshe Jarden and Aharon Razon, *Pseudo algebraically closed
fields over rings*, Israel Journal of Mathematics 86 (1994), 1–35,
Proposition 5.2, p.19 in the author's PDF:
https://www.math.tau.ac.il/~jarden/Articles/paper60.pdf
That proposition proves the general finitely generated-field statement from
Manin–Grauert–Samuel and Faltings. In characteristic zero its condition (b)
(not birational to a curve over a finite field) is automatic.

A nonsingular degree-d plane curve has genus (d-1)(d-2)/2; d≥4 gives genus≥3.
This classical genus calculation is included in the specialized external
statement, rather than being disguised as a new internal proof.
-/

noncomputable section
namespace LambdaCantor.Last

def SmoothHomogeneousPlanePolynomial (polynomial : MvPolynomial (Fin 3) ℝ)
    (degree : ℕ) : Prop :=
  polynomial.IsHomogeneous degree ∧
    ∀ coordinates : Fin 3 → ℂ,
      (∃ index, coordinates index ≠ 0) →
      MvPolynomial.eval₂ (Complex.ofRealHom) coordinates polynomial = 0 →
      ∃ index, MvPolynomial.eval₂ (Complex.ofRealHom) coordinates
        (MvPolynomial.pderiv index polynomial) ≠ 0

namespace External

/-- General smooth plane-curve Mordell theorem over an arbitrary finitely
generated real subfield. This is an explicitly registered external theorem. -/
axiom mordell_smooth_plane_curve
    (field : Subfield ℝ) (generators : Set ℝ) (finite_generators : generators.Finite)
    (generated : field = Subfield.closure generators)
    (polynomial : MvPolynomial (Fin 3) ℝ) (degree : ℕ) (degree_large : 4 ≤ degree)
    (coefficients : ∀ monomial, polynomial.coeff monomial ∈ field)
    (smooth : SmoothHomogeneousPlanePolynomial polynomial degree) :
    {point : ℝ × ℝ | point.1 ∈ field ∧ point.2 ∈ field ∧
      MvPolynomial.eval ![point.1, point.2, (1 : ℝ)] polynomial = 0}.Finite

end External

def fermatPlanePolynomial (degree : ℕ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.X 0 ^ degree + MvPolynomial.X 1 ^ degree - MvPolynomial.X 2 ^ degree

theorem fermatPlanePolynomial_homogeneous (degree : ℕ) :
    (fermatPlanePolynomial degree).IsHomogeneous degree := by
  exact ((MvPolynomial.isHomogeneous_X_pow 0 degree).add
    (MvPolynomial.isHomogeneous_X_pow 1 degree)).sub
      (MvPolynomial.isHomogeneous_X_pow 2 degree)

theorem fermatPlanePolynomial_smooth {degree : ℕ} (degree_positive : 0 < degree) :
    SmoothHomogeneousPlanePolynomial (fermatPlanePolynomial degree) degree := by
  refine ⟨fermatPlanePolynomial_homogeneous degree, ?_⟩
  intro coordinates nonzero _
  obtain ⟨index, coordinate_nonzero⟩ := nonzero
  have degree_nonzero : (degree : ℂ) ≠ 0 := by exact_mod_cast degree_positive.ne'
  refine ⟨index, ?_⟩
  fin_cases index
  · change coordinates 0 ≠ 0 at coordinate_nonzero
    simp [fermatPlanePolynomial, MvPolynomial.pderiv_X, degree_nonzero, coordinate_nonzero]
  · change coordinates 1 ≠ 0 at coordinate_nonzero
    simp [fermatPlanePolynomial, MvPolynomial.pderiv_X, degree_nonzero, coordinate_nonzero]
  · change coordinates 2 ≠ 0 at coordinate_nonzero
    simp [fermatPlanePolynomial, MvPolynomial.pderiv_X, degree_nonzero, coordinate_nonzero]

theorem fermatPlanePolynomial_coefficients (field : Subfield ℝ) (degree : ℕ) :
    ∀ monomial, (fermatPlanePolynomial degree).coeff monomial ∈ field := by
  intro monomial
  simp only [fermatPlanePolynomial, MvPolynomial.coeff_sub, MvPolynomial.coeff_add,
    MvPolynomial.coeff_X_pow]
  split_ifs <;> simp
  all_goals exact field.add_mem field.one_mem field.one_mem

/-- Finiteness is derived from the general curve theorem after checking
the homogeneous Fermat equation, its nonsingularity, and its coefficients. -/
theorem finite_fermat_points_parameterField {degree : ℕ} (degree_large : 4 ≤ degree)
    (ratio : ℝ) :
    {point : ℝ × ℝ | point.1 ∈ parameterField ratio ∧ point.2 ∈ parameterField ratio ∧
      point.1 ^ degree + point.2 ^ degree = 1}.Finite := by
  have finite_points := External.mordell_smooth_plane_curve
    (parameterField ratio) {ratio} (Set.finite_singleton ratio)
    (parameterField_eq_closure ratio) (fermatPlanePolynomial degree) degree degree_large
    (fermatPlanePolynomial_coefficients (parameterField ratio) degree)
    (fermatPlanePolynomial_smooth (by omega))
  convert finite_points using 1
  ext point
  simp [fermatPlanePolynomial, sub_eq_zero]

end LambdaCantor.Last
