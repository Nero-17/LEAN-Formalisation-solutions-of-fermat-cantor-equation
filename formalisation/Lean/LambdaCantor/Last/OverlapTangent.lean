import LambdaCantor.Last.OverlapCoreNeighborhood

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

/-- Tangent transfer for the complete overlap core. This form uses no narrow
inequality on the slope; the actual affine strict-return construction is its
explicit input. -/
theorem positive_dimension_of_tangent_branching_overlap
    {ratio slope : ℝ} (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hslope : 0 ≤ slope) (hcore : (affineOverlapCore ratio slope).Nonempty)
    (hreturns : ∀ value ∈ affineOverlapCore ratio slope, ∃ pair : ReturnPair,
      linearWordReturn ratio (positiveLinear slope) (pair.word false) value ∈
        interior (affineOverlapCore ratio slope) ∧
      linearWordReturn ratio (positiveLinear slope) (pair.word true) value ∈
        interior (affineOverlapCore ratio slope))
    (function : (ℝ × ℝ) → ℝ) (level : ℝ) (point : ℝ × ℝ)
    (hderivative : HasStrictFDerivAt function (positiveLinearContinuous slope) point)
    (hbranching : ∀ minimumDepth : ℕ, ∃ word : List (Bool × Bool),
      minimumDepth ≤ word.length ∧ point ∈ wordCylinder ratio word ∧
        BranchingCylinder ratio function level word) :
    0 < dimH {value : ℝ × ℝ | value ∈ cantorDust ratio ∧ function value = level} := by
  have hless : ratio < 1 := by linarith
  obtain ⟨threshold, hthreshold, neighborhood, hopen, hcontains, hcriterion⟩ :=
    local_source_criterion ratio hpositive hhalf (positiveLinearContinuous slope)
      (affineOverlapCore ratio slope) (isCompact_affineOverlapCore ratio slope) hcore hreturns
  obtain ⟨margin, hmargin, hmargin_mem⟩ :=
    affineOverlapCore_neighborhood_margin ratio slope neighborhood hopen hcontains
  let bound : ℝ≥0 := ⟨min threshold margin / 2, by positivity⟩
  have hbound_positive : 0 < bound := by
    change 0 < min threshold margin / 2
    positivity
  have hbound_threshold : (bound : ℝ) < threshold := by
    change min threshold margin / 2 < threshold
    linarith [min_le_left threshold margin]
  have hbound_margin : (bound : ℝ) < margin := by
    change min threshold margin / 2 < margin
    linarith [min_le_right threshold margin]
  obtain ⟨minimumDepth, hsmall⟩ := strict_derivative_cylinder_error hpositive hless
    hderivative bound hbound_positive
  obtain ⟨word, hdepth, hpoint, firstDigit, secondDigit, hdifferent,
    first, second, hfirst, hsecond, hfirstLevel, hsecondLevel⟩ := hbranching minimumDepth
  have hlipschitz := hsmall word hdepth hpoint
  obtain ⟨extension, hextension, hagreement⟩ := hlipschitz.extend_real
  have hnormalized := normalizedError_lipschitz hextension (ratio ^ word.length)
    (pow_pos hpositive _) (wordMap ratio word 0)
  have herror : ∀ value ∈ cantorDust ratio,
      |normalizedError extension (ratio ^ word.length) (wordMap ratio word 0) value| ≤ bound := by
    intro value hvalue
    have hdist := hnormalized.dist_le_mul value 0
    rw [normalizedError_zero, Real.dist_eq, sub_zero] at hdist
    exact hdist.trans (mul_le_of_le_one_right bound.coe_nonneg
      (dust_dist_le_one hpositive.le hless hvalue
        ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩))
  have hfirst_bounds := perturbed_child_level_bounds hpositive.le hless hslope
    (normalizedError extension (ratio ^ word.length) (wordMap ratio word 0)) herror
    firstDigit hfirst
    (normalized_fibre_equation hpositive (positiveLinearContinuous slope) function extension word
      hagreement level (wordMap_mem_dust hpositive.le hless [firstDigit] hfirst) hfirstLevel)
  have hsecond_bounds := perturbed_child_level_bounds hpositive.le hless hslope
    (normalizedError extension (ratio ^ word.length) (wordMap ratio word 0)) herror
    secondDigit hsecond
    (normalized_fibre_equation hpositive (positiveLinearContinuous slope) function extension word
      hagreement level (wordMap_mem_dust hpositive.le hless [secondDigit] hsecond) hsecondLevel)
  apply hcriterion bound hbound_threshold function level word hlipschitz
  exact hmargin_mem bound _ hbound_margin firstDigit secondDigit hdifferent
    hfirst_bounds.1 hfirst_bounds.2 hsecond_bounds.1 hsecond_bounds.2

end LambdaCantor.Last
