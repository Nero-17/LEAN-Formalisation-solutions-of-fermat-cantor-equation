import LambdaCantor.Integer.ExternalFermat
import LambdaCantor.Integer.IrrationalTangentSelection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace LambdaCantor.Integer

noncomputable def fermatTangent (n : ℕ) (point : ℝ × ℝ) : ℝ :=
  point.2^(n-1)/point.1^(n-1)

theorem fermat_tangent_strict_of_first_lt (n : ℕ) (exponent : 2 ≤ n)
    (p q : ℝ × ℝ) (px : 0 < p.1) (py : 0 < p.2)
    (qx : 0 < q.1) (qy : 0 < q.2)
    (pequation : p.1^n+p.2^n=1) (qequation : q.1^n+q.2^n=1)
    (first : p.1 < q.1) : fermatTangent n q < fermatTangent n p := by
  have nonzero : n ≠ 0 := by omega
  have predecessor : n-1 ≠ 0 := by omega
  have firstPowers : p.1^n < q.1^n :=
    (pow_lt_pow_iff_left₀ px.le qx.le nonzero).2 first
  have secondPowers : q.2^n < p.2^n := by linarith
  have second : q.2 < p.2 :=
    (pow_lt_pow_iff_left₀ qy.le py.le nonzero).1 secondPowers
  unfold fermatTangent
  apply (div_lt_div_iff₀ (pow_pos qx _) (pow_pos px _)).2
  calc
    q.2^(n-1)*p.1^(n-1) < p.2^(n-1)*p.1^(n-1) :=
      mul_lt_mul_of_pos_right
        ((pow_lt_pow_iff_left₀ qy.le py.le predecessor).2 second) (pow_pos px _)
    _ ≤ p.2^(n-1)*q.1^(n-1) :=
      mul_le_mul_of_nonneg_left
        ((pow_lt_pow_iff_left₀ px.le qx.le predecessor).2 first).le (by positivity)

theorem fermat_tangent_injective (n : ℕ) (exponent : 2 ≤ n)
    (source : Set (ℝ × ℝ))
    (positive : ∀ p ∈ source, 0 < p.1 ∧ 0 < p.2)
    (equation : ∀ p ∈ source, p.1^n+p.2^n=1) :
    Set.InjOn (fermatTangent n) source := by
  intro p hp q hq equal
  obtain ⟨px, py⟩ := positive p hp
  obtain ⟨qx, qy⟩ := positive q hq
  have first : p.1 = q.1 := by
    rcases lt_trichotomy p.1 q.1 with less | same | greater
    · have strict := fermat_tangent_strict_of_first_lt n exponent p q px py qx qy
        (equation p hp) (equation q hq) less
      rw [equal] at strict
      exact False.elim (lt_irrefl _ strict)
    · exact same
    · have strict := fermat_tangent_strict_of_first_lt n exponent q p qx qy px py
        (equation q hq) (equation p hp) greater
      rw [equal] at strict
      exact False.elim (lt_irrefl _ strict)
  apply Prod.ext first
  apply (pow_left_inj₀ py.le qy.le (by omega : n ≠ 0)).1
  have pe := equation p hp
  have qe := equation q hq
  rw [first] at pe
  linarith

/-- The precise Fermat-source perfectness/irrational-tangent selection step.
Source construction and isolated-point rationality remain explicit hypotheses.
The only external axiom used is the registered Fermat's Last Theorem. -/
theorem fermat_source_has_irrational_tangent (n : ℕ) (exponent : 3 ≤ n)
    (source : Set (ℝ × ℝ)) (compact : IsCompact source) (nonempty : source.Nonempty)
    (positive : ∀ p ∈ source, 0 < p.1 ∧ 0 < p.2)
    (equation : ∀ p ∈ source, p.1^n+p.2^n=1)
    (isolated_rational : ∀ p : source, IsOpen ({p} : Set source) →
      (∃ x : ℚ, (x : ℝ)=p.val.1) ∧ (∃ y : ℚ, (y : ℝ)=p.val.2)) :
    ∃ p ∈ source, ∀ rational : ℚ, fermatTangent n p ≠ (rational : ℝ) := by
  apply compact_source_has_irrational_tangent source compact nonempty
  · intro p isolated
    obtain ⟨px, py⟩ := positive p.val p.property
    obtain ⟨rationalX, rationalY⟩ := isolated_rational p isolated
    exact positive_rational_coordinates_not_on_fermat n exponent p.val.1 p.val.2
      px py rationalX rationalY (equation p.val p.property)
  · exact fermat_tangent_injective n (by omega) source positive equation

/-- Different cylinder depths multiply the physical tangent by a fixed
nonzero scale. Irrational selection is performed for that normalized tangent
directly, so no inference about arbitrary rescaling of an irrational is used. -/
theorem fermat_source_has_irrational_scaled_tangent (n : ℕ) (exponent : 3 ≤ n)
    (source : Set (ℝ × ℝ)) (compact : IsCompact source) (nonempty : source.Nonempty)
    (positive : ∀ p ∈ source, 0 < p.1 ∧ 0 < p.2)
    (equation : ∀ p ∈ source, p.1^n+p.2^n=1)
    (isolated_rational : ∀ p : source, IsOpen ({p} : Set source) →
      (∃ x : ℚ, (x : ℝ)=p.val.1) ∧ (∃ y : ℚ, (y : ℝ)=p.val.2))
    (scale : ℝ) (nonzero : scale ≠ 0) :
    ∃ p ∈ source, ∀ rational : ℚ, scale*fermatTangent n p ≠ (rational : ℝ) := by
  apply compact_source_has_irrational_tangent source compact nonempty
  · intro p isolated
    obtain ⟨px,py⟩ := positive p.val p.property
    obtain ⟨rationalX,rationalY⟩ := isolated_rational p isolated
    exact positive_rational_coordinates_not_on_fermat n exponent p.val.1 p.val.2
      px py rationalX rationalY (equation p.val p.property)
  · intro p hp q hq equal
    exact fermat_tangent_injective n (by omega) source positive equation hp hq
      (mul_left_cancel₀ nonzero equal)

end LambdaCantor.Integer
