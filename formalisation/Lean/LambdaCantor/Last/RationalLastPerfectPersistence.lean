import LambdaCantor.Last.RationalLastPerfectPositive
import LambdaCantor.Last.RationalLastFermatParameterRegularity

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

theorem perfect_open_phase_fibre_positive_dimension_persist_parameter {ratio slope : ℝ}
    (above_third : (1/3 : ℝ) < ratio) (less_half : ratio < 1/2)
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope)
    (outside : slope ∉ parameterField ratio)
    (family : ℝ → (ℝ × ℝ) → ℝ)
    (joint_continuous : Continuous (fun value : ℝ × (ℝ × ℝ) => family value.1 value.2))
    {source : Set (ℝ × ℝ)} (perfect : Perfect source)
    (contained : source ⊆ {value | value ∈ cantorDust ratio ∧ family ratio value = 0})
    {point : ℝ × ℝ} (point_mem : point ∈ source)
    (derivative : HasStrictFDerivAt (family ratio) (positiveLinearContinuous slope) point)
    (joint_smooth : ContDiffAt ℝ 2
      (fun value : ℝ × (ℝ × ℝ) => family value.1 value.2) (ratio, point)) :
    ∀ᶠ perturbed in 𝓝 ratio,
      0 < dimH {value | value ∈ cantorDust perturbed ∧ family perturbed value = 0} := by
  have positive : 0 < ratio := by linarith
  have bounds := periodicity_phase_weak_overlaps above_third less_half phase
  obtain ⟨jointLinear, joint_derivative, spatial_derivative⟩ :=
    joint_strict_derivative_with_given_spatial_derivative family ratio point joint_smooth
      (positiveLinearContinuous slope) derivative
  exact perfect_fibre_positive_dimension_persist_parameter positive less_half (by linarith [bounds.1])
    (periodicity_phase_affine_overlap_nonempty above_third less_half phase)
    (periodicity_phase_affine_strict_returns above_third less_half phase outside)
    family joint_continuous perfect contained point_mem derivative jointLinear joint_derivative spatial_derivative

theorem contDiff_prefixExchangeMap_joint (digit : Bool) :
    ContDiff ℝ 2 (fun value : ℝ × (ℝ × ℝ) => (value.1, prefixExchangeMap value.1 digit value.2)) := by
  cases digit <;> simp only [prefixExchangeMap, scalarWordMap, Bool.false_eq_true, if_false,
    if_true, zero_add] <;> fun_prop

/-- All normalized external-field phases admit a parameter-stable finite
entrance, including the coordinate/depth exchange. The perfect set is only
an input at the original parameter. -/
theorem normalized_perfect_fibre_positive_dimension_persist_parameter {ratio slope : ℝ}
    (above_critical : (Real.sqrt 3-1)/2 ≤ ratio) (less_half : ratio < 1/2)
    (normalized : 1 ≤ slope ∧ slope < 1/ratio) (outside : slope ∉ parameterField ratio)
    (family : ℝ → (ℝ × ℝ) → ℝ)
    (joint_continuous : Continuous (fun value : ℝ × (ℝ × ℝ) => family value.1 value.2))
    {source : Set (ℝ × ℝ)} (perfect : Perfect source) (compact : IsCompact source)
    (contained : source ⊆ {value | value ∈ cantorDust ratio ∧ family ratio value = 0})
    {point : ℝ × ℝ} (point_mem : point ∈ source)
    (first_outside : point.1 ∉ parameterField ratio) (second_outside : point.2 ∉ parameterField ratio)
    (derivative : HasStrictFDerivAt (family ratio) (positiveLinearContinuous slope) point)
    (joint_smooth : ContDiffAt ℝ 2
      (fun value : ℝ × (ℝ × ℝ) => family value.1 value.2) (ratio, point)) :
    ∀ᶠ perturbed in 𝓝 ratio,
      0 < dimH {value | value ∈ cantorDust perturbed ∧ family perturbed value = 0} := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have positive : 0 < ratio := by nlinarith
  have above_third : (1/3 : ℝ) < ratio := by nlinarith
  have less_one : ratio < 1 := by linarith
  rcases normalized_external_slope_in_periodicity_phase above_critical less_half normalized outside with
    small | mixed | exchanged
  · exact perfect_open_phase_fibre_positive_dimension_persist_parameter above_third less_half (Or.inl small)
      outside family joint_continuous perfect contained point_mem derivative joint_smooth
  · exact perfect_open_phase_fibre_positive_dimension_persist_parameter above_third less_half (Or.inr mixed)
      outside family joint_continuous perfect contained point_mem derivative joint_smooth
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
    let exchangedFamily := fun perturbed value => family perturbed (prefixExchangeMap perturbed digit value)/(ratio*slope)
    have inverse_outside : 1/(ratio*slope) ∉ parameterField ratio := by
      simpa [one_div] using inv_not_mem_parameterField
        (mul_not_mem_parameterField (ratio_mem_parameterField ratio) positive.ne' outside)
    have exchanged_derivative : HasStrictFDerivAt (exchangedFamily ratio)
        (positiveLinearContinuous (1/(ratio*slope))) preimage :=
      exchangedNormalizedFunction_hasStrictFDerivAt positive slope_positive digit (family ratio)
        (point := preimage) (by rw [representation]; exact derivative)
    have local_zero : localPerfect ⊆ {value | value ∈ cantorDust ratio ∧ exchangedFamily ratio value = 0} := by
      intro value membership
      have local_value := local_contained membership
      refine ⟨local_value.1, ?_⟩
      dsimp [exchangedFamily]
      rw [(contained local_value.2).2]
      simp
    have exchanged_continuous : Continuous
        (fun value : ℝ × (ℝ × ℝ) => exchangedFamily value.1 value.2) :=
      (joint_continuous.comp (contDiff_prefixExchangeMap_joint digit).continuous).div_const _
    have base_smooth : ContDiffAt ℝ 2
        (fun value : ℝ × (ℝ × ℝ) => family value.1 value.2)
        (ratio, prefixExchangeMap ratio digit preimage) := by
      rw [representation]
      exact joint_smooth
    have exchanged_smooth : ContDiffAt ℝ 2
        (fun value : ℝ × (ℝ × ℝ) => exchangedFamily value.1 value.2) (ratio, preimage) := by
      have composition : ContDiffAt ℝ 2
          (fun value : ℝ × (ℝ × ℝ) => family value.1 (prefixExchangeMap value.1 digit value.2))
          (ratio, preimage) := by
        simpa only [Function.comp_def] using
          (ContDiffAt.comp
            (g := fun value : ℝ × (ℝ × ℝ) => family value.1 value.2)
            (f := fun value : ℝ × (ℝ × ℝ) =>
              (value.1, prefixExchangeMap value.1 digit value.2))
            (ratio, preimage) base_smooth
            ((contDiff_prefixExchangeMap_joint digit).contDiffAt (x := (ratio, preimage))))
      change ContDiffAt ℝ 2
        (fun value : ℝ × (ℝ × ℝ) =>
          family value.1 (prefixExchangeMap value.1 digit value.2)/(ratio*slope)) (ratio, preimage)
      exact composition.div_const (ratio*slope)
    have persistent := perfect_open_phase_fibre_positive_dimension_persist_parameter above_third less_half
      (Or.inl exchanged) inverse_outside exchangedFamily exchanged_continuous local_perfect local_zero
      preimage_local exchanged_derivative exchanged_smooth
    filter_upwards [persistent, lt_mem_nhds positive, gt_mem_nhds less_one] with
      perturbed dimension perturbed_positive perturbed_less_one
    apply dimension.trans_le ((prefixExchangeMap_antilipschitz perturbed_positive digit).le_dimH_image _ |>.trans
      (dimH_mono ?_))
    rintro value ⟨tail, tail_mem, rfl⟩
    refine ⟨prefixExchangeMap_mem_dust perturbed_positive.le perturbed_less_one digit tail_mem.1, ?_⟩
    have equation := tail_mem.2
    dsimp [exchangedFamily] at equation
    exact (div_eq_zero_iff.mp equation).resolve_right (mul_ne_zero positive.ne' slope_positive.ne')

/-- The actual rational perfect-set construction persists on a two-sided
parameter neighborhood. Its geometric/arithmetic premises concern only the
original intersection. -/
theorem actual_fermat_positive_dimension_persist_of_infinite_of_finite_isolated {exponent ratio : ℝ}
    (exponent_gt_one : 1 < exponent)
    (above_critical : (Real.sqrt 3-1)/2 ≤ ratio) (less_half : ratio < 1/2)
    (compact : IsCompact (intersection exponent ratio))
    (infinite : (intersection exponent ratio).Infinite)
    (finite_isolated : (isolatedPoints (intersection exponent ratio)).Finite) :
    ∀ᶠ perturbed in 𝓝 ratio, 0 < dimH (intersection exponent perturbed) := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have positive : 0 < ratio := by nlinarith
  have less_one : ratio < 1 := by linarith
  obtain ⟨firstWord, secondWord, tail, slope, height, localPerfect,
      perfect, local_compact, tail_mem, contained, slope_lower, slope_upper, slope_outside,
      height_positive, first_outside, second_outside, first_interior, second_interior, _, derivative⟩ :=
    selected_perfect_actual_fermat_normalization exponent_gt_one positive less_half compact infinite finite_isolated
  have tail_dust := (contained tail_mem).1
  have first_positive : 0 < scalarWordMap ratio firstWord tail.1 := by
    have bounds := scalarWordMap_bounds positive.le less_one firstWord (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    rw [scalarWordMap_affine ratio firstWord tail.1]
    exact add_pos_of_nonneg_of_pos bounds.1
      (mul_pos (pow_pos positive firstWord.length) first_interior.1)
  have second_positive : 0 < scalarWordMap ratio secondWord tail.2 := by
    have bounds := scalarWordMap_bounds positive.le less_one secondWord (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    rw [scalarWordMap_affine ratio secondWord tail.2]
    exact add_pos_of_nonneg_of_pos bounds.1
      (mul_pos (pow_pos positive secondWord.length) second_interior.1)
  have persistent := normalized_perfect_fibre_positive_dimension_persist_parameter above_critical less_half
    ⟨slope_lower, slope_upper⟩ slope_outside
    (fun perturbed => normalizedFermatPrefix exponent perturbed firstWord secondWord height)
    (continuous_normalizedFermatPrefix_joint (by linarith) firstWord secondWord height)
    perfect local_compact contained tail_mem first_outside second_outside derivative
    (contDiffAt_normalizedFermatPrefix_joint firstWord secondWord tail first_positive second_positive)
  filter_upwards [persistent, lt_mem_nhds positive, gt_mem_nhds less_one] with
    perturbed dimension perturbed_positive perturbed_less_one
  apply dimension.trans_le ((anisotropicPrefixMap_antilipschitz perturbed_positive firstWord secondWord).le_dimH_image _ |>.trans
    (dimH_mono ?_))
  rintro value ⟨tail, tail_mem, rfl⟩
  exact normalizedFermatPrefix_zero_mapsTo perturbed_positive.le perturbed_less_one
    height_positive.ne' firstWord secondWord tail_mem

end LambdaCantor.Last
