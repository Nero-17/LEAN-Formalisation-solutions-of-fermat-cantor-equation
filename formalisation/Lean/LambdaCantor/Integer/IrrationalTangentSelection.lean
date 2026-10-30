import LambdaCantor.Integer.CountableFibres

namespace LambdaCantor.Integer

/-- A nonempty compact metric source without isolated points is uncountable.
This is the precise topological step after rational isolated points have been
excluded by Fermat's Last Theorem. -/
theorem compact_without_isolated_uncountable {X : Type*} [MetricSpace X]
    (source : Set X) (compact : IsCompact source) (nonempty : source.Nonempty)
    (no_isolated : ∀ p : source, ¬ IsOpen ({p} : Set source)) :
    ¬ source.Countable := by
  intro countable
  letI : Countable source := countable.to_subtype
  letI : CompleteSpace source := compact.isComplete.completeSpace_coe
  letI : Nonempty source := Set.nonempty_coe_sort.mpr nonempty
  have dense := isolated_points_dense (X := source)
  obtain ⟨p, hp⟩ := dense.nonempty
  exact no_isolated p hp

/-- An injective tangent-ratio map on an uncountable source takes an irrational
value. All rational values form a countable set, independently of the geometry. -/
theorem exists_irrational_tangent {X : Type*} (source : Set X)
    (uncountable : ¬ source.Countable) (tangent : X → ℝ)
    (injective : Set.InjOn tangent source) :
    ∃ p ∈ source, ∀ rational : ℚ, tangent p ≠ (rational : ℝ) := by
  classical
  by_contra absent
  push_neg at absent
  have maps : Set.MapsTo tangent source (Set.range ((↑) : ℚ → ℝ)) := by
    intro p hp
    obtain ⟨rational, equality⟩ := absent p hp
    exact ⟨rational, equality.symm⟩
  exact uncountable (maps.countable_of_injOn injective (Set.countable_range _))

theorem compact_source_has_irrational_tangent {X : Type*} [MetricSpace X]
    (source : Set X) (compact : IsCompact source) (nonempty : source.Nonempty)
    (no_isolated : ∀ p : source, ¬ IsOpen ({p} : Set source))
    (tangent : X → ℝ) (injective : Set.InjOn tangent source) :
    ∃ p ∈ source, ∀ rational : ℚ, tangent p ≠ (rational : ℝ) :=
  exists_irrational_tangent source
    (compact_without_isolated_uncountable source compact nonempty no_isolated)
    tangent injective

end LambdaCantor.Integer
