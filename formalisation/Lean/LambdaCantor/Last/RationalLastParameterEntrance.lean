import LambdaCantor.Last.ReturnParameterCriterion
import LambdaCantor.Last.RationalLastParameterError
import LambdaCantor.Last.PerfectBranching
import LambdaCantor.Last.OverlapCoreNeighborhood

noncomputable section
open Filter
open scoped NNReal Topology
namespace LambdaCantor.Last

/-- A perfect fibre at the original contraction supplies a finite entrance.
Joint differentiability moves that same entrance, while the finite return
criterion supplies the perturbed binary construction. -/
theorem perfect_fibre_positive_dimension_persist_parameter
    {ratio slope : ℝ} (positive : 0 < ratio) (less_half : ratio < 1/2)
    (slope_nonnegative : 0 ≤ slope) (core_nonempty : (affineOverlapCore ratio slope).Nonempty)
    (returns : ∀ value ∈ affineOverlapCore ratio slope, ∃ pair : ReturnPair,
      linearWordReturn ratio (positiveLinear slope) (pair.word false) value ∈
        interior (affineOverlapCore ratio slope) ∧
      linearWordReturn ratio (positiveLinear slope) (pair.word true) value ∈
        interior (affineOverlapCore ratio slope))
    (family : ℝ → (ℝ × ℝ) → ℝ)
    (joint_continuous : Continuous (fun value : ℝ × (ℝ × ℝ) => family value.1 value.2))
    {source : Set (ℝ × ℝ)} (perfect : Perfect source)
    (contained : source ⊆ {value | value ∈ cantorDust ratio ∧ family ratio value = 0})
    {point : ℝ × ℝ} (point_mem : point ∈ source)
    (derivative : HasStrictFDerivAt (family ratio) (positiveLinearContinuous slope) point)
    (jointLinear : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ)
    (joint_derivative : HasStrictFDerivAt
      (fun value : ℝ × (ℝ × ℝ) => family value.1 value.2) jointLinear (ratio, point))
    (spatial_derivative : ∀ increment : ℝ × ℝ,
      jointLinear (0, increment) = positiveLinearContinuous slope increment) :
    ∀ᶠ perturbed in 𝓝 ratio,
      0 < dimH {value | value ∈ cantorDust perturbed ∧ family perturbed value = 0} := by
  have less_one : ratio < 1 := by linarith
  obtain ⟨threshold, threshold_positive, neighborhood, neighborhood_open, core_contained, persistent⟩ :=
    strict_return_criterion_persist_parameter positive less_half (positiveLinearContinuous slope)
      (affineOverlapCore ratio slope) (isCompact_affineOverlapCore ratio slope) core_nonempty returns
  obtain ⟨margin, margin_positive, near_core⟩ :=
    affineOverlapCore_neighborhood_margin ratio slope neighborhood neighborhood_open core_contained
  let bound : ℝ≥0 := ⟨min threshold margin/2, by positivity⟩
  have bound_positive : 0 < bound := by change 0 < min threshold margin/2; positivity
  have bound_threshold : (bound : ℝ) < threshold := by
    change min threshold margin/2 < threshold
    linarith [min_le_left threshold margin]
  have bound_margin : (bound : ℝ) < margin := by
    change min threshold margin/2 < margin
    linarith [min_le_right threshold margin]
  obtain ⟨baseDepth, base_error⟩ := strict_derivative_cylinder_error positive less_one derivative bound bound_positive
  obtain ⟨movingDepth, moving_error⟩ := joint_strict_derivative_moving_cylinder_error positive less_one family point
    jointLinear (positiveLinearContinuous slope) joint_derivative spatial_derivative bound bound_positive
  obtain ⟨word, depth_lower, point_in_word, firstDigit, secondDigit, different,
      first, second, first_dust, second_dust, first_source, second_source⟩ :=
    perfect_fibre_deep_branching_with_points positive less_half (family ratio) 0 source perfect contained
      point_mem (max baseDepth movingDepth)
  have base_lipschitz := base_error word (by omega) point_in_word
  obtain ⟨extension, extension_lipschitz, agreement⟩ := base_lipschitz.extend_real
  have normalized_lipschitz := normalizedError_lipschitz extension_lipschitz (ratio^word.length)
    (pow_pos positive _) (wordMap ratio word 0)
  have error_bound : ∀ value ∈ cantorDust ratio,
      |normalizedError extension (ratio^word.length) (wordMap ratio word 0) value| ≤ bound := by
    intro value membership
    have distance_bound := normalized_lipschitz.dist_le_mul value 0
    rw [normalizedError_zero, Real.dist_eq, sub_zero] at distance_bound
    exact distance_bound.trans (mul_le_of_le_one_right bound.coe_nonneg
      (dust_dist_le_one positive.le less_one membership ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩))
  have first_bounds := perturbed_child_level_bounds positive.le less_one slope_nonnegative
    (normalizedError extension (ratio^word.length) (wordMap ratio word 0)) error_bound firstDigit first_dust
    (normalized_fibre_equation positive (positiveLinearContinuous slope) (family ratio) extension word agreement 0
      (wordMap_mem_dust positive.le less_one [firstDigit] first_dust) (contained first_source).2)
  have second_bounds := perturbed_child_level_bounds positive.le less_one slope_nonnegative
    (normalizedError extension (ratio^word.length) (wordMap ratio word 0)) error_bound secondDigit second_dust
    (normalized_fibre_equation positive (positiveLinearContinuous slope) (family ratio) extension word agreement 0
      (wordMap_mem_dust positive.le less_one [secondDigit] second_dust) (contained second_source).2)
  have entrance_mem : (0-family ratio (wordMap ratio word 0))/ratio^word.length ∈ neighborhood :=
    near_core bound _ bound_margin firstDigit secondDigit different
      first_bounds.1 first_bounds.2 second_bounds.1 second_bounds.2
  have corner_continuous : Continuous (fun perturbed : ℝ =>
      family perturbed (wordMap perturbed word 0)) :=
    joint_continuous.comp (continuous_id.prodMk (continuous_wordMap_zero_parameter word))
  have entrance_continuous : ContinuousAt (fun perturbed : ℝ =>
      (0-family perturbed (wordMap perturbed word 0))/perturbed^word.length) ratio :=
    (continuousAt_const.sub corner_continuous.continuousAt).div
      (continuousAt_id.pow word.length) (pow_pos positive _).ne'
  have entrance_eventual := entrance_continuous.eventually
    (neighborhood_open.mem_nhds entrance_mem)
  filter_upwards [persistent, entrance_eventual, moving_error word (by omega) point_in_word] with
    perturbed perturbed_criterion entrance moving_lipschitz
  have perturbed_positive := perturbed_criterion.1
  have perturbed_less_one : perturbed < 1 := by linarith [perturbed_criterion.2.1]
  obtain ⟨movingExtension, movingExtension_lipschitz, moving_agreement⟩ := moving_lipschitz.extend_real
  have normalized_dimension := perturbed_criterion.2.2 bound bound_threshold
    (normalizedError movingExtension (perturbed^word.length) (wordMap perturbed word 0))
    (normalizedError_lipschitz movingExtension_lipschitz _ (pow_pos perturbed_positive _) _).lipschitzOnWith
    (normalizedError_zero _ _ _) _ entrance
  apply positive_dimension_of_cylinder_fibre perturbed_positive perturbed_less_one word (family perturbed) 0
  apply normalized_dimension.trans_le (dimH_mono ?_)
  intro value membership
  refine ⟨membership.1, ?_⟩
  have equation := membership.2
  have original := normalized_fibre_equation perturbed_positive (positiveLinearContinuous slope)
    (family perturbed) movingExtension word moving_agreement
    (family perturbed (wordMap perturbed word value)) membership.1 rfl
  rw [equation] at original
  have cleared := congrArg (fun scalar : ℝ => scalar*perturbed^word.length) original
  simp only [div_mul_cancel₀ _ (pow_pos perturbed_positive word.length).ne'] at cleared
  linarith

end LambdaCantor.Last
