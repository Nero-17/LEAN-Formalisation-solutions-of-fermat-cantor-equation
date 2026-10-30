import LambdaCantor.Last.LocalSource
import LambdaCantor.Last.BranchingLevels

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

/-- Two different first children of the indicated actual cylinder meet the fibre. -/
def BranchingCylinder (ratio : ℝ) (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (word : List (Bool × Bool)) : Prop :=
  ∃ firstDigit secondDigit : Bool × Bool, firstDigit ≠ secondDigit ∧
    ∃ first second : ℝ × ℝ, first ∈ cantorDust ratio ∧ second ∈ cantorDust ratio ∧
      function (wordMap ratio word (wordMap ratio [firstDigit] first)) = level ∧
      function (wordMap ratio word (wordMap ratio [secondDigit] second)) = level

theorem normalized_fibre_equation {ratio : ℝ} (hpositive : 0 < ratio)
    (linear : (ℝ × ℝ) →L[ℝ] ℝ) (function extension : (ℝ × ℝ) → ℝ)
    (word : List (Bool × Bool))
    (hagreement : Set.EqOn (fun value => function value - linear value) extension (wordCylinder ratio word))
    (level : ℝ) {point : ℝ × ℝ} (hpoint : point ∈ cantorDust ratio)
    (hlevel : function (wordMap ratio word point) = level) :
    linear point + normalizedError extension (ratio ^ word.length) (wordMap ratio word 0) point =
      (level - function (wordMap ratio word 0)) / ratio ^ word.length := by
  have hcorner : wordMap ratio word 0 ∈ wordCylinder ratio word :=
    ⟨0, ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩, rfl⟩
  have himage : wordMap ratio word point ∈ wordCylinder ratio word := ⟨point, hpoint, rfl⟩
  have hcorner_eq : linear (wordMap ratio word 0) + extension (wordMap ratio word 0) =
      function (wordMap ratio word 0) := by rw [← hagreement hcorner]; ring
  have himage_eq : linear (wordMap ratio word point) + extension (wordMap ratio word point) = level := by
    rw [← hagreement himage]
    linarith
  have identity := restriction_identity linear.toLinearMap extension (ratio ^ word.length) level
    (ne_of_gt (pow_pos hpositive _)) (wordMap ratio word 0) point
  simp only [restrictPoint, ← wordMap_affine, returnLevel] at identity
  change linear (wordMap ratio word point) + extension (wordMap ratio word point) - level =
    ratio ^ word.length * (linear point +
      normalizedError extension (ratio ^ word.length) (wordMap ratio word 0) point -
      (level - (linear (wordMap ratio word 0) + extension (wordMap ratio word 0))) /
        ratio ^ word.length) at identity
  rw [himage_eq, hcorner_eq, sub_self] at identity
  exact sub_eq_zero.mp ((mul_eq_zero.mp identity.symm).resolve_left (ne_of_gt (pow_pos hpositive _)))

/-- The analytic step of the nonlinear criterion. Arbitrarily deep genuine
branching cylinders through a strict differentiability point yield positive dimension. -/
theorem positive_dimension_of_tangent_branching
    {ratio slope : ℝ} (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hslopes : StrictSlopeConditions ratio slope)
    (function : (ℝ × ℝ) → ℝ) (level : ℝ) (point : ℝ × ℝ)
    (hderivative : HasStrictFDerivAt function (positiveLinearContinuous slope) point)
    (hbranching : ∀ minimumDepth : ℕ, ∃ word : List (Bool × Bool),
      minimumDepth ≤ word.length ∧ point ∈ wordCylinder ratio word ∧
        BranchingCylinder ratio function level word) :
    0 < dimH {value : ℝ × ℝ | value ∈ cantorDust ratio ∧ function value = level} := by
  have hless_one : ratio < 1 := by linarith
  have hinterval : 1 - ratio ≤ slope + ratio := by linarith [hslopes.1]
  obtain ⟨threshold, hthreshold, neighborhood, hopen, hcontains, hcriterion⟩ :=
    local_source_criterion ratio hpositive hhalf (positiveLinearContinuous slope)
      (Set.Icc (1 - ratio) (slope + ratio)) isCompact_Icc (Set.nonempty_Icc.mpr hinterval)
      (fun value hvalue => linear_closed_central_strict_returns hpositive hhalf hslopes hvalue)
  obtain ⟨margin, hmargin, hmargin_mem⟩ := open_interval_neighborhood_margin hinterval hopen hcontains
  let bound : ℝ≥0 := ⟨min threshold margin / 2, by positivity⟩
  have hbound_pos : 0 < bound := by change 0 < min threshold margin / 2; positivity
  have hbound_threshold : (bound : ℝ) < threshold := by
    change min threshold margin / 2 < threshold
    linarith [min_le_left threshold margin]
  have hbound_margin : (bound : ℝ) < margin := by
    change min threshold margin / 2 < margin
    linarith [min_le_right threshold margin]
  obtain ⟨minimumDepth, hsmall_error⟩ := strict_derivative_cylinder_error hpositive hless_one
    hderivative bound hbound_pos
  obtain ⟨word, hdepth, hpoint, firstDigit, secondDigit, hdifferent,
    first, second, hfirst, hsecond, hfirstLevel, hsecondLevel⟩ := hbranching minimumDepth
  have hlipschitz := hsmall_error word hdepth hpoint
  obtain ⟨extension, hextension, hagreement⟩ := hlipschitz.extend_real
  have herror_lipschitz := normalizedError_lipschitz hextension (ratio ^ word.length)
    (pow_pos hpositive _) (wordMap ratio word 0)
  have herror_bound : ∀ value ∈ cantorDust ratio,
      |normalizedError extension (ratio ^ word.length) (wordMap ratio word 0) value| ≤ bound := by
    intro value hvalue
    have hdist := herror_lipschitz.dist_le_mul value 0
    rw [normalizedError_zero, Real.dist_eq, sub_zero] at hdist
    exact hdist.trans (mul_le_of_le_one_right bound.coe_nonneg
      (dust_dist_le_one hpositive.le hless_one hvalue
        ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩))
  have hlevel_bounds := branching_level_bounds hpositive.le hless_one hslopes.1
    (normalizedError extension (ratio ^ word.length) (wordMap ratio word 0)) herror_bound
    firstDigit secondDigit hdifferent first second hfirst hsecond
    (normalized_fibre_equation hpositive (positiveLinearContinuous slope) function extension word hagreement level
      (wordMap_mem_dust hpositive.le hless_one [firstDigit] hfirst) hfirstLevel)
    (normalized_fibre_equation hpositive (positiveLinearContinuous slope) function extension word hagreement level
      (wordMap_mem_dust hpositive.le hless_one [secondDigit] hsecond) hsecondLevel)
  apply hcriterion bound hbound_threshold function level word hlipschitz
  apply hmargin_mem
  · linarith [hlevel_bounds.1]
  · linarith [hlevel_bounds.2]

end LambdaCantor.Last
