import LambdaCantor.Last.RationalLastPerfect
import LambdaCantor.Last.RationalLastNormalizationDecoding
import LambdaCantor.Last.RationalLastNormalizationFermat

noncomputable section
open scoped Topology
namespace LambdaCantor.Last

theorem perfect_image_of_continuous_injective_of_compact
    {source : Set (ℝ × ℝ)} (perfect : Perfect source) (compact : IsCompact source)
    (mapping : (ℝ × ℝ) → ℝ × ℝ) (continuous_mapping : Continuous mapping)
    (injective : Function.Injective mapping) : Perfect (mapping '' source) := by
  refine ⟨(compact.image continuous_mapping).isClosed, ?_⟩
  apply preperfect_iff_nhds.mpr
  rintro _ ⟨point, membership, rfl⟩ neighborhood neighborhood_mem
  obtain ⟨other, ⟨other_near, other_mem⟩, different⟩ :=
    preperfect_iff_nhds.mp perfect.acc point membership (mapping ⁻¹' neighborhood)
      (continuous_mapping.continuousAt.preimage_mem_nhds neighborhood_mem)
  exact ⟨mapping other, ⟨other_near, ⟨other, other_mem, rfl⟩⟩,
    fun equal => different (injective equal)⟩

/-- Restrict the original perfect set inside the actual prefix rectangle,
then decode it. Only the original contraction is involved. -/
theorem perfect_subset_in_anisotropic_prefix
    {ratio : ℝ} (positive : 0 < ratio) (less_half : ratio < 1/2)
    (firstWord secondWord : List Bool) {tail : ℝ × ℝ}
    (tail_interior : tail.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ tail.2 ∈ Set.Ioo (0 : ℝ) 1)
    {source : Set (ℝ × ℝ)} (perfect : Perfect source) (compact : IsCompact source)
    (contained : source ⊆ cantorDust ratio)
    (point_mem : anisotropicPrefixMap ratio firstWord secondWord tail ∈ source) :
    ∃ localPerfect : Set (ℝ × ℝ), Perfect localPerfect ∧ IsCompact localPerfect ∧
      tail ∈ localPerfect ∧ localPerfect ⊆
        {value | value ∈ cantorDust ratio ∧
          anisotropicPrefixMap ratio firstWord secondWord value ∈ source} := by
  let inverse := anisotropicPrefixInverse ratio firstWord secondWord
  let neighborhood : Set (ℝ × ℝ) := inverse ⁻¹'
    (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)
  let localSource := closure (neighborhood ∩ source)
  have continuous_inverse : Continuous inverse :=
    continuous_anisotropicPrefixInverse ratio firstWord secondWord
  have neighborhood_open : IsOpen neighborhood :=
    (isOpen_Ioo.prod isOpen_Ioo).preimage continuous_inverse
  have point_neighborhood : anisotropicPrefixMap ratio firstWord secondWord tail ∈ neighborhood := by
    change anisotropicPrefixInverse ratio firstWord secondWord
      (anisotropicPrefixMap ratio firstWord secondWord tail) ∈
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)
    rw [anisotropicPrefixInverse_map positive]
    exact tail_interior
  have local_perfect : Perfect localSource :=
    (perfect.acc.open_inter neighborhood_open).perfect_closure
  have local_contained : localSource ⊆ source :=
    closure_minimal Set.inter_subset_right perfect.closed
  have local_compact : IsCompact localSource :=
    compact.of_isClosed_subset isClosed_closure local_contained
  have closed_bounds : IsClosed (inverse ⁻¹'
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :=
    (isClosed_Icc.prod isClosed_Icc).preimage continuous_inverse
  have local_bounds : localSource ⊆ inverse ⁻¹'
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    apply closure_minimal _ closed_bounds
    intro point membership
    exact ⟨⟨membership.1.1.1.le, membership.1.1.2.le⟩,
      ⟨membership.1.2.1.le, membership.1.2.2.le⟩⟩
  have inverse_injective : Function.Injective inverse := by
    intro first second equal
    have mapped := congrArg (anisotropicPrefixMap ratio firstWord secondWord) equal
    simpa only [inverse, anisotropicPrefixMap_inverse positive] using mapped
  refine ⟨inverse '' localSource,
    perfect_image_of_continuous_injective_of_compact local_perfect local_compact
      inverse continuous_inverse inverse_injective,
    local_compact.image continuous_inverse, ?_, ?_⟩
  · refine ⟨anisotropicPrefixMap ratio firstWord secondWord tail,
      subset_closure ⟨point_neighborhood, point_mem⟩, ?_⟩
    exact anisotropicPrefixInverse_map positive firstWord secondWord tail
  · rintro _ ⟨point, point_local, rfl⟩
    have point_actual := contained (local_contained point_local)
    have unit_bounds := local_bounds point_local
    have mapped := anisotropicPrefixMap_inverse positive firstWord secondWord point
    have first_hull : point.1 ∈ Set.Icc
        (scalarWordMap ratio firstWord 0) (scalarWordMap ratio firstWord 1) := by
      have coordinates := congrArg Prod.fst mapped
      change scalarWordMap ratio firstWord (inverse point).1 = point.1 at coordinates
      rw [← coordinates, scalarWordMap_affine ratio firstWord (inverse point).1,
        scalarWordMap_affine ratio firstWord 1]
      constructor <;> nlinarith [mul_nonneg (pow_nonneg positive.le firstWord.length) unit_bounds.1.1,
        mul_le_mul_of_nonneg_left unit_bounds.1.2 (pow_nonneg positive.le firstWord.length)]
    have second_hull : point.2 ∈ Set.Icc
        (scalarWordMap ratio secondWord 0) (scalarWordMap ratio secondWord 1) := by
      have coordinates := congrArg Prod.snd mapped
      change scalarWordMap ratio secondWord (inverse point).2 = point.2 at coordinates
      rw [← coordinates, scalarWordMap_affine ratio secondWord (inverse point).2,
        scalarWordMap_affine ratio secondWord 1]
      constructor <;> nlinarith [mul_nonneg (pow_nonneg positive.le secondWord.length) unit_bounds.2.1,
        mul_le_mul_of_nonneg_left unit_bounds.2.2 (pow_nonneg positive.le secondWord.length)]
    refine ⟨anisotropicPrefixInverse_mem_dust_of_hull positive less_half firstWord secondWord
      point_actual first_hull second_hull, ?_⟩
    change anisotropicPrefixMap ratio firstWord secondWord
      (anisotropicPrefixInverse ratio firstWord secondWord point) ∈ source
    rw [mapped]
    exact local_contained point_local

theorem perfect_fermat_subset_in_actual_prefix
    {exponent ratio height : ℝ} (positive : 0 < ratio) (less_half : ratio < 1/2)
    (firstWord secondWord : List Bool) {tail : ℝ × ℝ}
    (tail_interior : tail.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ tail.2 ∈ Set.Ioo (0 : ℝ) 1)
    {source : Set (ℝ × ℝ)} (perfect : Perfect source) (compact : IsCompact source)
    (contained : source ⊆ intersection exponent ratio)
    (point_mem : anisotropicPrefixMap ratio firstWord secondWord tail ∈ source) :
    ∃ localPerfect : Set (ℝ × ℝ), Perfect localPerfect ∧ IsCompact localPerfect ∧
      tail ∈ localPerfect ∧ localPerfect ⊆
        {value | value ∈ cantorDust ratio ∧
          normalizedFermatPrefix exponent ratio firstWord secondWord height value = 0} := by
  obtain ⟨localPerfect, local_perfect, local_compact, tail_local, local_contained⟩ :=
    perfect_subset_in_anisotropic_prefix positive less_half firstWord secondWord tail_interior
      perfect compact (fun value membership => ⟨(contained membership).1, (contained membership).2.1⟩)
      point_mem
  refine ⟨localPerfect, local_perfect, local_compact, tail_local, ?_⟩
  intro value membership
  have local_value := local_contained membership
  have actual := contained local_value.2
  refine ⟨local_value.1, ?_⟩
  have equation := actual.2.2
  change (scalarWordMap ratio firstWord value.1)^exponent+
    (scalarWordMap ratio secondWord value.2)^exponent = 1 at equation
  unfold normalizedFermatPrefix
  rw [equation]
  simp

/-- The arithmetic/topological selection is realized on an actual normalized
Fermat rectangle, with a local perfect set containing the selected tail.
The source compactness, infinitude and isolated-point finiteness are the
three explicit inputs still supplied by the rational endpoint/classification
chains. No perturbed-parameter perfect set is asserted. -/
theorem selected_perfect_actual_fermat_normalization {exponent ratio : ℝ}
    (exponent_gt_one : 1 < exponent) (positive : 0 < ratio) (less_half : ratio < 1/2)
    (compact : IsCompact (intersection exponent ratio))
    (infinite : (intersection exponent ratio).Infinite)
    (finite_isolated : (isolatedPoints (intersection exponent ratio)).Finite) :
    ∃ (firstWord secondWord : List Bool) (tail : ℝ × ℝ) (slope height : ℝ)
      (localPerfect : Set (ℝ × ℝ)),
      Perfect localPerfect ∧ IsCompact localPerfect ∧ tail ∈ localPerfect ∧
      localPerfect ⊆ {value | value ∈ cantorDust ratio ∧
        normalizedFermatPrefix exponent ratio firstWord secondWord height value = 0} ∧
      1 ≤ slope ∧ slope < 1/ratio ∧ slope ∉ parameterField ratio ∧ 0 < height ∧
      tail.1 ∉ parameterField ratio ∧ tail.2 ∉ parameterField ratio ∧
      tail.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ tail.2 ∈ Set.Ioo (0 : ℝ) 1 ∧
      ContDiffAt ℝ 2 (normalizedFermatPrefix exponent ratio firstWord secondWord height) tail ∧
      HasStrictFDerivAt (normalizedFermatPrefix exponent ratio firstWord secondWord height)
        (positiveLinearContinuous slope) tail := by
  have less_one : ratio < 1 := by linarith
  obtain ⟨source, perfect, source_compact, contained, point, point_mem,
      first_positive, second_positive, first_outside, second_outside, tangent_outside⟩ :=
    perfect_fermat_tangent_selection (ratio := ratio) exponent_gt_one compact infinite finite_isolated
      (fun value membership =>
        ⟨(cantorSet_subset_unitInterval positive.le less_one membership.1).1,
          (cantorSet_subset_unitInterval positive.le less_one membership.2.1).1⟩)
      (fun _ membership => membership.2.2) (countable_parameterField ratio)
  let actualPoint : intersection exponent ratio := ⟨point, contained point_mem⟩
  obtain ⟨firstWord, secondWord, tail, slope, height, tail_mem, representation, slope_identity,
      slope_lower, slope_upper, height_positive, zero, smooth, derivative⟩ :=
    exists_actual_fermat_prefix_normalization exponent_gt_one positive less_one actualPoint
      first_positive second_positive
  have tail_fields_excluded : tail.1 ∉ parameterField ratio ∧ tail.2 ∉ parameterField ratio := by
    constructor
    · intro first_mem
      apply first_outside
      have coordinate := scalarWordMap_mem_parameterField firstWord first_mem
      have actual_coordinate := congrArg Prod.fst representation
      change scalarWordMap ratio firstWord tail.1 = point.1 at actual_coordinate
      rw [← actual_coordinate]
      exact coordinate
    · intro second_mem
      apply second_outside
      have coordinate := scalarWordMap_mem_parameterField secondWord second_mem
      have actual_coordinate := congrArg Prod.snd representation
      change scalarWordMap ratio secondWord tail.2 = point.2 at actual_coordinate
      rw [← actual_coordinate]
      exact coordinate
  have tail_interior : tail.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ tail.2 ∈ Set.Ioo (0 : ℝ) 1 := by
    have first_bounds := cantorSet_subset_unitInterval positive.le less_one tail_mem.1
    have second_bounds := cantorSet_subset_unitInterval positive.le less_one tail_mem.2
    have strict_bounds : ∀ coordinate : ℝ, coordinate ∈ Set.Icc (0 : ℝ) 1 →
        coordinate ∉ parameterField ratio → coordinate ∈ Set.Ioo (0 : ℝ) 1 := by
      intro coordinate bounds outside
      constructor
      · exact lt_of_le_of_ne bounds.1 (fun equal => outside (equal ▸ (parameterField ratio).zero_mem))
      · exact lt_of_le_of_ne bounds.2 (fun equal => outside (equal.symm ▸ (parameterField ratio).one_mem))
    exact ⟨strict_bounds _ first_bounds tail_fields_excluded.1,
      strict_bounds _ second_bounds tail_fields_excluded.2⟩
  obtain ⟨localPerfect, local_perfect, local_compact, tail_local, local_contained⟩ :=
    perfect_fermat_subset_in_actual_prefix (height := height) positive less_half firstWord secondWord
      tail_interior perfect source_compact contained (by simpa only [representation] using point_mem)
  refine ⟨firstWord, secondWord, tail, slope, height, localPerfect,
    local_perfect, local_compact, tail_local, local_contained,
    slope_lower, slope_upper, ?_, height_positive, tail_fields_excluded.1, tail_fields_excluded.2,
    tail_interior.1, tail_interior.2, smooth, derivative⟩
  rw [slope_identity]
  exact normalized_prefix_slope_not_mem_parameterField positive tangent_outside _ _

end LambdaCantor.Last
