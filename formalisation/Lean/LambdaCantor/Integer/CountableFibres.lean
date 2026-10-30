import LambdaCantor.Integer.RationalFibres
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.ProperSpace.Real

namespace LambdaCantor.Integer

/-- Isolated points are dense in a countable Baire T1 space. This supplies
the compact-countable step of the irrational-fibre argument directly from
mathlib's Baire theorem, without a new external assumption. -/
theorem isolated_points_dense {X : Type*} [TopologicalSpace X] [T1Space X]
    [BaireSpace X] [Countable X] :
    Dense {x : X | IsOpen ({x} : Set X)} := by
  have hd : Dense (⋃ x : X, interior ({x} : Set X)) :=
    dense_iUnion_interior_of_closed (fun _ => isClosed_singleton) (by ext; simp)
  apply hd.mono
  intro x hx
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hx
  have heq : x = y := Set.mem_singleton_iff.mp (interior_subset hy)
  subst y
  have hi : interior ({x} : Set X) = {x} := by
    apply Set.Subset.antisymm interior_subset
    intro z hz
    have hz' : z = x := Set.mem_singleton_iff.mp hz
    simpa only [hz'] using hy
  change IsOpen ({x} : Set X)
  rw [← hi]
  exact isOpen_interior

theorem subsingleton_of_isolated_unique {X : Type*} [TopologicalSpace X] [T1Space X]
    [BaireSpace X] [Countable X]
    (unique : ∀ x y : X, IsOpen ({x} : Set X) → IsOpen ({y} : Set X) → x = y) :
    Subsingleton X := by
  have hs : ({x : X | IsOpen ({x} : Set X)} : Set X).Subsingleton := by
    intro x hx y hy
    exact unique x y hx hy
  have hc := hs.closure
  rw [(isolated_points_dense (X := X)).closure_eq] at hc
  exact ⟨fun x y => hc (Set.mem_univ x) (Set.mem_univ y)⟩

/-- Once isolated points are known to have rational coordinates, an affine
fibre at an irrational slope is a singleton or uncountable. The hypothesis
about isolated points is the exact digital-analysis obligation, not an axiom. -/
theorem affine_fibre_subsingleton_or_uncountable
    (fibre : Set (ℝ × ℝ)) (compact : IsCompact fibre) (r level : ℝ)
    (irrational : ∀ q : ℚ, r ≠ (q : ℝ))
    (on_level : ∀ p ∈ fibre, r * p.1 + p.2 = level)
    (isolated_rational : ∀ p : fibre, IsOpen ({p} : Set fibre) →
      ∃ x y : ℚ, (x : ℝ) = p.val.1 ∧ (y : ℝ) = p.val.2) :
    fibre.Subsingleton ∨ ¬ fibre.Countable := by
  classical
  by_cases hc : fibre.Countable
  · left
    letI : Countable fibre := hc.to_subtype
    letI : CompleteSpace fibre := compact.isComplete.completeSpace_coe
    have hu : Subsingleton fibre := subsingleton_of_isolated_unique (by
      intro p q hp hq
      obtain ⟨x₁, y₁, hx₁, hy₁⟩ := isolated_rational p hp
      obtain ⟨x₂, y₂, hx₂, hy₂⟩ := isolated_rational q hq
      have heq : r * (x₁ : ℝ) + y₁ = r * (x₂ : ℝ) + y₂ := by
        rw [hx₁, hy₁, hx₂, hy₂, on_level p.val p.property, on_level q.val q.property]
      obtain ⟨hx, hy⟩ := rational_points_unique_in_irrational_fibre r irrational
        x₁ y₁ x₂ y₂ heq
      apply Subtype.ext
      apply Prod.ext
      · rw [← hx₁, ← hx₂, hx]
      · rw [← hy₁, ← hy₂, hy])
    intro p hp q hq
    exact congrArg Subtype.val (@Subsingleton.elim fibre hu (⟨p,hp⟩ : fibre) (⟨q,hq⟩ : fibre))
  · exact Or.inr hc

end LambdaCantor.Integer
