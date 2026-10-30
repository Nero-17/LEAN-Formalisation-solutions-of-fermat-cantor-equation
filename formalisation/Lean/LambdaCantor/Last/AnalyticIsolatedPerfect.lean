import LambdaCantor.Integer.CountableFibres
import Mathlib.Topology.MetricSpace.Perfect
import LambdaCantor.Last.ArithmeticField

noncomputable section
namespace LambdaCantor.Last

/-- Isolation is expressed in the relative topology of the actual fibre. -/
def isolatedPoints {X : Type*} [TopologicalSpace X] (source : Set X) : Set source :=
  {point | IsOpen ({point} : Set source)}

/-- An infinite compact metric set with only finitely many isolated points
is uncountable. The finite isolated set is closed and, under countability,
Baire's theorem makes it dense, which would force the whole set to be finite. -/
theorem uncountable_of_infinite_of_finite_isolated
    {X : Type*} [MetricSpace X] {source : Set X}
    (compact : IsCompact source) (infinite : source.Infinite)
    (finite_isolated : (isolatedPoints source).Finite) : ¬ source.Countable := by
  intro countable
  letI : Countable source := countable.to_subtype
  letI : CompleteSpace source := compact.isComplete.completeSpace_coe
  have dense : Dense (isolatedPoints source) :=
    LambdaCantor.Integer.isolated_points_dense
  have all_isolated : isolatedPoints source = Set.univ := by
    rw [← finite_isolated.isClosed.closure_eq]
    exact dense.closure_eq
  have finite_source : (Set.univ : Set source).Finite := all_isolated ▸ finite_isolated
  have finite_range := finite_source.image (fun point : source => (point : X))
  have range_eq : (fun point : source => (point : X)) '' Set.univ = source := by
    ext point
    simp
  exact infinite (range_eq ▸ finite_range)

theorem exists_perfect_subset_of_infinite_of_finite_isolated
    {X : Type*} [MetricSpace X] [SecondCountableTopology X] {source : Set X}
    (compact : IsCompact source) (infinite : source.Infinite)
    (finite_isolated : (isolatedPoints source).Finite) :
    ∃ perfectSubset : Set X,
      Perfect perfectSubset ∧ perfectSubset.Nonempty ∧ perfectSubset ⊆ source :=
  exists_perfect_nonempty_of_isClosed_of_not_countable compact.isClosed
    (uncountable_of_infinite_of_finite_isolated compact infinite finite_isolated)

/-- Selection avoids a countable family of forbidden values and a countable
family of forbidden points at the same time. -/
theorem exists_point_avoiding_countable
    {X Y : Type*} {source forbiddenPoints : Set X} {forbiddenValues : Set Y}
    (uncountable : ¬ source.Countable) (points_countable : forbiddenPoints.Countable)
    (values_countable : forbiddenValues.Countable) (function : X → Y)
    (injective : Set.InjOn function source) :
    ∃ point ∈ source, point ∉ forbiddenPoints ∧ function point ∉ forbiddenValues := by
  classical
  by_contra absent
  push_neg at absent
  have remaining_countable : (source \ forbiddenPoints).Countable := by
    apply Set.MapsTo.countable_of_injOn (f := function)
    · intro point membership
      exact absent point membership.1 membership.2
    · exact injective.mono Set.sdiff_subset
    · exact values_countable
  apply uncountable
  apply (remaining_countable.union points_countable).mono
  intro point membership
  by_cases forbidden : point ∈ forbiddenPoints
  · exact Or.inr forbidden
  · exact Or.inl ⟨membership, forbidden⟩

/-- This is the arithmetic selection used before normalizing a tangent:
both the field and all cylinder endpoints are countable obstructions. -/
theorem exists_point_with_tangent_outside_parameterField
    {X : Type*} {source forbiddenPoints : Set X} {ratio : ℝ}
    (uncountable : ¬ source.Countable) (points_countable : forbiddenPoints.Countable)
    (tangent : X → ℝ) (injective : Set.InjOn tangent source) :
    ∃ point ∈ source, point ∉ forbiddenPoints ∧ tangent point ∉ parameterField ratio :=
  exists_point_avoiding_countable uncountable points_countable
    (countable_parameterField ratio) tangent injective

end LambdaCantor.Last
