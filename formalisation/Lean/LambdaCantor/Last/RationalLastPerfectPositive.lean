import LambdaCantor.Last.RationalLastPerfectNormalization
import LambdaCantor.Last.RationalLastNormalizationExchange
import LambdaCantor.Last.AnalyticIsolatedPhases
import LambdaCantor.Last.AnalyticIsolatedOpenPhases
import LambdaCantor.Last.PerfectTangent

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

theorem perfect_subset_in_prefixExchange {ratio : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2) (digit : Bool)
    {tail : ℝ × ℝ}
    (tail_interior : tail.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ tail.2 ∈ Set.Ioo (0 : ℝ) 1)
    {source : Set (ℝ × ℝ)} (perfect : Perfect source) (compact : IsCompact source)
    (contained : source ⊆ cantorDust ratio)
    (point_mem : prefixExchangeMap ratio digit tail ∈ source) :
    ∃ localPerfect : Set (ℝ × ℝ), Perfect localPerfect ∧ IsCompact localPerfect ∧
      tail ∈ localPerfect ∧ localPerfect ⊆
        {value | value ∈ cantorDust ratio ∧ prefixExchangeMap ratio digit value ∈ source} := by
  let swappedSource := Prod.swap '' source
  have swapped_perfect : Perfect swappedSource :=
    perfect_image_of_continuous_injective_of_compact perfect compact Prod.swap continuous_swap
      (fun _ _ equal => by simpa using congrArg Prod.swap equal)
  have swapped_compact : IsCompact swappedSource := compact.image continuous_swap
  have swapped_dust : swappedSource ⊆ cantorDust ratio := by
    rintro _ ⟨point, membership, rfl⟩
    exact ⟨(contained membership).2, (contained membership).1⟩
  have prefix_mem : anisotropicPrefixMap ratio [digit] [] tail ∈ swappedSource := by
    refine ⟨prefixExchangeMap ratio digit tail, point_mem, ?_⟩
    rfl
  obtain ⟨localPerfect, local_perfect, local_compact, tail_local, local_contained⟩ :=
    perfect_subset_in_anisotropic_prefix positive less_half [digit] [] tail_interior
      swapped_perfect swapped_compact swapped_dust prefix_mem
  refine ⟨localPerfect, local_perfect, local_compact, tail_local, ?_⟩
  intro value membership
  have value_local := local_contained membership
  refine ⟨value_local.1, ?_⟩
  obtain ⟨original, original_mem, equal⟩ := value_local.2
  have swapped_equal := congrArg Prod.swap equal
  change original = prefixExchangeMap ratio digit value at swapped_equal
  exact swapped_equal ▸ original_mem

theorem prefixExchangeMap_antilipschitz {ratio : ℝ} (positive : 0 < ratio) (digit : Bool) :
    AntilipschitzWith
      (⟨max (ratio^([digit] : List Bool).length)⁻¹ (ratio^([] : List Bool).length)⁻¹,
        le_max_of_le_left (inv_nonneg.mpr (pow_nonneg positive.le _))⟩ : ℝ≥0)
      (prefixExchangeMap ratio digit) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro first second
  simpa only [Prod.dist_eq, prefixExchangeMap, anisotropicPrefixMap, scalarWordMap, max_comm] using
    (anisotropicPrefixMap_antilipschitz positive [digit] []).le_mul_dist first second

theorem perfect_open_phase_fibre_positive_dimension {ratio slope : ℝ}
    (above_third : (1/3 : ℝ) < ratio) (less_half : ratio < 1/2)
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope)
    (outside : slope ∉ parameterField ratio)
    (function : (ℝ × ℝ) → ℝ) {source : Set (ℝ × ℝ)}
    (perfect : Perfect source)
    (contained : source ⊆ {value | value ∈ cantorDust ratio ∧ function value = 0})
    {point : ℝ × ℝ} (point_mem : point ∈ source)
    (derivative : HasStrictFDerivAt function (positiveLinearContinuous slope) point) :
    0 < dimH {value | value ∈ cantorDust ratio ∧ function value = 0} := by
  have positive : 0 < ratio := by linarith
  have bounds := periodicity_phase_weak_overlaps above_third less_half phase
  exact perfect_fibre_positive_dimension_of_strict_returns positive less_half (by linarith [bounds.1])
    (periodicity_phase_affine_overlap_nonempty above_third less_half phase)
    (periodicity_phase_affine_strict_returns above_third less_half phase outside)
    function 0 source perfect contained point_mem derivative

/-- The normalized selected perfect fibre gives positive dimension in all
open phases, including the actual coordinate/depth exchange. -/
theorem normalized_perfect_fibre_positive_dimension {ratio slope : ℝ}
    (above_critical : (Real.sqrt 3-1)/2 ≤ ratio) (less_half : ratio < 1/2)
    (normalized : 1 ≤ slope ∧ slope < 1/ratio) (outside : slope ∉ parameterField ratio)
    (function : (ℝ × ℝ) → ℝ) {source : Set (ℝ × ℝ)}
    (perfect : Perfect source) (compact : IsCompact source)
    (contained : source ⊆ {value | value ∈ cantorDust ratio ∧ function value = 0})
    {point : ℝ × ℝ} (point_mem : point ∈ source)
    (first_outside : point.1 ∉ parameterField ratio)
    (second_outside : point.2 ∉ parameterField ratio)
    (derivative : HasStrictFDerivAt function (positiveLinearContinuous slope) point) :
    0 < dimH {value | value ∈ cantorDust ratio ∧ function value = 0} := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have positive : 0 < ratio := by nlinarith
  have above_third : (1/3 : ℝ) < ratio := by nlinarith
  have less_one : ratio < 1 := by linarith
  rcases normalized_external_slope_in_periodicity_phase above_critical less_half normalized outside with
    small | mixed | exchanged
  · exact perfect_open_phase_fibre_positive_dimension above_third less_half (Or.inl small)
      outside function perfect contained point_mem derivative
  · exact perfect_open_phase_fibre_positive_dimension above_third less_half (Or.inr mixed)
      outside function perfect contained point_mem derivative
  · obtain ⟨digit, preimage, preimage_dust, representation⟩ :=
      exists_prefixExchange_preimage positive.le less_one (contained point_mem).1
    have preimage_outside : preimage.1 ∉ parameterField ratio ∧ preimage.2 ∉ parameterField ratio := by
      constructor
      · intro membership
        apply second_outside
        have coordinate := congrArg Prod.snd representation
        change scalarWordMap ratio [digit] preimage.1 = point.2 at coordinate
        rw [← coordinate]
        exact scalarWordMap_mem_parameterField [digit] membership
      · intro membership
        apply first_outside
        have coordinate := congrArg Prod.fst representation
        change preimage.2 = point.1 at coordinate
        exact coordinate ▸ membership
    have strict_bounds : ∀ coordinate : ℝ, coordinate ∈ cantorSet ratio →
        coordinate ∉ parameterField ratio → coordinate ∈ Set.Ioo (0 : ℝ) 1 := by
      intro coordinate membership field_outside
      have bounds := cantorSet_subset_unitInterval positive.le less_one membership
      constructor
      · exact lt_of_le_of_ne bounds.1
          (fun equal => field_outside (equal ▸ (parameterField ratio).zero_mem))
      · exact lt_of_le_of_ne bounds.2
          (fun equal => field_outside (equal.symm ▸ (parameterField ratio).one_mem))
    obtain ⟨localPerfect, local_perfect, _, preimage_local, local_contained⟩ :=
      perfect_subset_in_prefixExchange positive less_half digit
        ⟨strict_bounds _ preimage_dust.1 preimage_outside.1,
          strict_bounds _ preimage_dust.2 preimage_outside.2⟩ perfect compact
        (fun value membership => (contained membership).1) (by rw [representation]; exact point_mem)
    have slope_positive : 0 < slope := by linarith [normalized.1]
    have inverse_outside : 1/(ratio*slope) ∉ parameterField ratio := by
      simpa [one_div] using inv_not_mem_parameterField
        (mul_not_mem_parameterField (ratio_mem_parameterField ratio) positive.ne' outside)
    have exchanged_derivative := exchangedNormalizedFunction_hasStrictFDerivAt positive slope_positive
      digit function (point := preimage) (by rw [representation]; exact derivative)
    have local_zero : localPerfect ⊆ {value | value ∈ cantorDust ratio ∧
        exchangedNormalizedFunction ratio slope digit function value = 0} := by
      intro value membership
      have local_value := local_contained membership
      refine ⟨local_value.1, ?_⟩
      unfold exchangedNormalizedFunction
      rw [(contained local_value.2).2]
      simp
    have dimension := perfect_open_phase_fibre_positive_dimension above_third less_half
      (Or.inl exchanged) inverse_outside (exchangedNormalizedFunction ratio slope digit function)
      local_perfect local_zero preimage_local exchanged_derivative
    apply dimension.trans_le ((prefixExchangeMap_antilipschitz positive digit).le_dimH_image _ |>.trans
      (dimH_mono ?_))
    rintro value ⟨tail, tail_mem, rfl⟩
    refine ⟨prefixExchangeMap_mem_dust positive.le less_one digit tail_mem.1, ?_⟩
    have equation := tail_mem.2
    unfold exchangedNormalizedFunction at equation
    exact (div_eq_zero_iff.mp equation).resolve_right
      (mul_ne_zero positive.ne' slope_positive.ne')

/-- Once the genuine endpoint infinitude and actual isolated-point finiteness
are supplied, the rational perfect-set route proves actual positivity at
every contraction at or above c. -/
theorem actual_fermat_positive_dimension_of_infinite_of_finite_isolated {exponent ratio : ℝ}
    (exponent_gt_one : 1 < exponent)
    (above_critical : (Real.sqrt 3-1)/2 ≤ ratio) (less_half : ratio < 1/2)
    (compact : IsCompact (intersection exponent ratio))
    (infinite : (intersection exponent ratio).Infinite)
    (finite_isolated : (isolatedPoints (intersection exponent ratio)).Finite) :
    0 < dimH (intersection exponent ratio) := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have positive : 0 < ratio := by nlinarith
  have less_one : ratio < 1 := by linarith
  obtain ⟨firstWord, secondWord, tail, slope, height, localPerfect,
      perfect, local_compact, tail_mem, contained, slope_lower, slope_upper, slope_outside,
      height_positive, first_outside, second_outside, _, _, _, derivative⟩ :=
    selected_perfect_actual_fermat_normalization exponent_gt_one positive less_half compact infinite finite_isolated
  have dimension := normalized_perfect_fibre_positive_dimension above_critical less_half
    ⟨slope_lower, slope_upper⟩ slope_outside
    (normalizedFermatPrefix exponent ratio firstWord secondWord height)
    perfect local_compact contained tail_mem first_outside second_outside derivative
  apply dimension.trans_le ((anisotropicPrefixMap_antilipschitz positive firstWord secondWord).le_dimH_image _ |>.trans
    (dimH_mono ?_))
  rintro value ⟨tail, tail_mem, rfl⟩
  exact normalizedFermatPrefix_zero_mapsTo positive.le less_one height_positive.ne' firstWord secondWord tail_mem

end LambdaCantor.Last
