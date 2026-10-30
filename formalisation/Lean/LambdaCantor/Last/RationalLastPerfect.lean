import LambdaCantor.Last.RationalLastTangent
import LambdaCantor.Basic
import LambdaCantor.Last.UncountableCoding

noncomputable section
namespace LambdaCantor.Last

theorem fermat_first_coordinate_injective {exponent : ℝ} (exponent_positive : 0 < exponent)
    {source : Set (ℝ × ℝ)}
    (nonnegative : ∀ point ∈ source, 0 ≤ point.1 ∧ 0 ≤ point.2)
    (on_level : ∀ point ∈ source, point.1 ^ exponent + point.2 ^ exponent = 1) :
    Set.InjOn Prod.fst source := by
  intro first first_mem second second_mem equal
  apply Prod.ext equal
  apply (Real.rpow_left_inj (nonnegative first first_mem).2
    (nonnegative second second_mem).2 exponent_positive.ne').mp
  have first_equation := on_level first first_mem
  have second_equation := on_level second second_mem
  rw [equal] at first_equation
  linarith

theorem fermat_second_coordinate_injective {exponent : ℝ} (exponent_positive : 0 < exponent)
    {source : Set (ℝ × ℝ)}
    (nonnegative : ∀ point ∈ source, 0 ≤ point.1 ∧ 0 ≤ point.2)
    (on_level : ∀ point ∈ source, point.1 ^ exponent + point.2 ^ exponent = 1) :
    Set.InjOn Prod.snd source := by
  intro first first_mem second second_mem equal
  apply Prod.ext ?_ equal
  apply (Real.rpow_left_inj (nonnegative first first_mem).1
    (nonnegative second second_mem).1 exponent_positive.ne').mp
  have first_equation := on_level first first_mem
  have second_equation := on_level second second_mem
  rw [equal] at first_equation
  linarith

theorem countable_coordinate_obstructions {exponent : ℝ} (exponent_positive : 0 < exponent)
    {source : Set (ℝ × ℝ)} {forbidden : Set ℝ}
    (nonnegative : ∀ point ∈ source, 0 ≤ point.1 ∧ 0 ≤ point.2)
    (on_level : ∀ point ∈ source, point.1 ^ exponent + point.2 ^ exponent = 1)
    (forbidden_countable : forbidden.Countable) :
    {point ∈ source | point.1 ∈ forbidden ∨ point.2 ∈ forbidden}.Countable := by
  have first_countable : {point ∈ source | point.1 ∈ forbidden}.Countable := by
    exact Set.MapsTo.countable_of_injOn
      (fun _ membership => membership.2)
      ((fermat_first_coordinate_injective exponent_positive nonnegative on_level).mono
        (fun _ membership => membership.1)) forbidden_countable
  have second_countable : {point ∈ source | point.2 ∈ forbidden}.Countable := by
    exact Set.MapsTo.countable_of_injOn
      (fun _ membership => membership.2)
      ((fermat_second_coordinate_injective exponent_positive nonnegative on_level).mono
        (fun _ membership => membership.1)) forbidden_countable
  apply (first_countable.union second_countable).mono
  rintro point ⟨membership, first_forbidden | second_forbidden⟩
  · exact Or.inl ⟨membership, first_forbidden⟩
  · exact Or.inr ⟨membership, second_forbidden⟩

/-- The full topological selection after geometric infinitude and arithmetic
finiteness. It produces a perfect compact source and a point with positive
coordinates, outside any prescribed countable coordinate obstruction, whose
tangent ratio is outside the generated field. This is deliberately separated
from the still-required proofs of infinitude and isolated-point finiteness. -/
theorem perfect_fermat_tangent_selection {exponent ratio : ℝ}
    (exponent_gt_one : 1 < exponent) {source : Set (ℝ × ℝ)}
    (compact : IsCompact source) (infinite : source.Infinite)
    (finite_isolated : (isolatedPoints source).Finite)
    (nonnegative : ∀ point ∈ source, 0 ≤ point.1 ∧ 0 ≤ point.2)
    (on_level : ∀ point ∈ source, point.1 ^ exponent + point.2 ^ exponent = 1)
    {forbidden : Set ℝ} (forbidden_countable : forbidden.Countable) :
    ∃ perfectSubset : Set (ℝ × ℝ), Perfect perfectSubset ∧ IsCompact perfectSubset ∧
      perfectSubset ⊆ source ∧ ∃ point ∈ perfectSubset,
        0 < point.1 ∧ 0 < point.2 ∧ point.1 ∉ forbidden ∧ point.2 ∉ forbidden ∧
          fermatTangentRatio exponent point ∉ parameterField ratio := by
  have exponent_positive : 0 < exponent := by linarith
  obtain ⟨perfectSubset, perfect, perfect_nonempty, contained⟩ :=
    exists_perfect_subset_of_infinite_of_finite_isolated compact infinite finite_isolated
  have perfect_uncountable : ¬ perfectSubset.Countable := by
    obtain ⟨coding, range_contained, _, injective⟩ :=
      perfect.exists_nat_bool_injection perfect_nonempty
    exact uncountable_of_injective_binary_coding coding injective
      (fun digits => range_contained ⟨digits, rfl⟩)
  let badCoordinates : Set ℝ := insert 0 forbidden
  have bad_countable : badCoordinates.Countable := forbidden_countable.insert 0
  have coordinate_bad_countable := countable_coordinate_obstructions exponent_positive
    (fun point membership => nonnegative point (contained membership))
    (fun point membership => on_level point (contained membership)) bad_countable
  let positiveSource : Set (ℝ × ℝ) :=
    {point ∈ perfectSubset | point.1 ∉ badCoordinates ∧ point.2 ∉ badCoordinates}
  have positive_uncountable : ¬ positiveSource.Countable := by
    intro countable
    apply perfect_uncountable
    apply (countable.union coordinate_bad_countable).mono
    intro point membership
    by_cases first_bad : point.1 ∈ badCoordinates
    · exact Or.inr ⟨membership, Or.inl first_bad⟩
    · by_cases second_bad : point.2 ∈ badCoordinates
      · exact Or.inr ⟨membership, Or.inr second_bad⟩
      · exact Or.inl ⟨membership, first_bad, second_bad⟩
  have positive : ∀ point ∈ positiveSource, 0 < point.1 ∧ 0 < point.2 := by
    intro point membership
    have bounds := nonnegative point (contained membership.1)
    constructor
    · exact lt_of_le_of_ne bounds.1 (by
        intro equal
        apply membership.2.1
        rw [← equal]
        exact Set.mem_insert 0 forbidden)
    · exact lt_of_le_of_ne bounds.2 (by
        intro equal
        apply membership.2.2
        rw [← equal]
        exact Set.mem_insert 0 forbidden)
  obtain ⟨point, membership, _, tangent_outside⟩ :=
    exists_point_with_tangent_outside_parameterField (ratio := ratio) positive_uncountable
      Set.countable_empty (fermatTangentRatio exponent)
      (fermatTangentRatio_injective exponent_gt_one positive
        (fun point membership => on_level point (contained membership.1)))
  refine ⟨perfectSubset, perfect, compact.of_isClosed_subset perfect.closed contained,
    contained, point, membership.1, (positive point membership).1,
    (positive point membership).2, ?_, ?_, tangent_outside⟩
  · exact fun forbidden_mem => membership.2.1 (Set.mem_insert_of_mem 0 forbidden_mem)
  · exact fun forbidden_mem => membership.2.2 (Set.mem_insert_of_mem 0 forbidden_mem)

end LambdaCantor.Last
