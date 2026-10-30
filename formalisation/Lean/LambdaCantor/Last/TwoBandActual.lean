import LambdaCantor.Last.TwoBandNonlinear
import LambdaCantor.Last.BranchingLevels

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

theorem normalized_corner_linear_error
    {ratio : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1)
    (function : (ℝ × ℝ) → ℝ) (linear : (ℝ × ℝ) →L[ℝ] ℝ)
    (word : List (Bool × Bool)) (bound : ℝ≥0)
    (hlipschitz : LipschitzOnWith bound (fun value => function value - linear value)
      (wordCylinder ratio word)) {point : ℝ × ℝ} (hpoint : point ∈ cantorDust ratio) :
    |(function (wordMap ratio word point) - function (wordMap ratio word 0)) /
      ratio ^ word.length - linear point| ≤ bound := by
  have hzero : (0 : ℝ × ℝ) ∈ cantorDust ratio :=
    ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩
  have hbound := hlipschitz.dist_le_mul (wordMap ratio word point) ⟨point, hpoint, rfl⟩
    (wordMap ratio word 0) ⟨0, hzero, rfl⟩
  rw [wordMap_distance, abs_of_pos hpositive, Real.dist_eq] at hbound
  have hdist := dust_dist_le_one hpositive.le hless hpoint hzero
  have hestimate : |(function (wordMap ratio word point) - linear (wordMap ratio word point)) -
      (function (wordMap ratio word 0) - linear (wordMap ratio word 0))| ≤
        (bound : ℝ) * ratio ^ word.length := by
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (pow_nonneg hpositive.le _) hdist) bound.coe_nonneg)
  have hidentity : (function (wordMap ratio word point) - function (wordMap ratio word 0)) /
      ratio ^ word.length - linear point =
      ((function (wordMap ratio word point) - linear (wordMap ratio word point)) -
        (function (wordMap ratio word 0) - linear (wordMap ratio word 0))) / ratio ^ word.length := by
    rw [wordMap_affine ratio word point, map_add, map_smul]
    simp only [smul_eq_mul]
    field_simp [ne_of_gt (pow_pos hpositive word.length)]
    <;> ring
  rw [hidentity, abs_div, abs_of_pos (pow_pos hpositive _), div_le_iff₀ (pow_pos hpositive _)]
  exact hestimate

/-- Every strict interior level has positive dimension under the new bands.
The normalized strict derivative is required only at Cantor points. Global
increment inequalities provide entrance; local strict returns provide dimension. -/
theorem positive_dimension_of_two_band_coordinate_growth
    {function : (ℝ × ℝ) → ℝ} {lowerS upperS lowerT upperT ratio level : ℝ}
    (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    (hcontinuous : Continuous function) (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hlowerS : 0 < lowerS) (hslope : upperS < lowerT)
    (hshell : (1 - ratio - ratio ^ 2) * upperS < ratio * lowerT)
    (houter : (1 - 2 * ratio) * upperS < ratio * lowerT)
    (hmiddle : (1 - 2 * ratio) * upperT < lowerS)
    (hderivatives : ∀ point ∈ cantorDust ratio, ∃ scale slope : ℝ,
      0 < scale ∧ TwoBandSlopes ratio slope ∧
      HasStrictFDerivAt (fun value => function value / scale) (positiveLinearContinuous slope) point)
    (hlevel : level ∈ Set.Ioo (function (0, 0)) (function (1, 1))) :
    0 < dimH {point | point ∈ cantorDust ratio ∧ function point = level} := by
  have hless : ratio < 1 := by linarith
  have hcover : ∀ parent : InteriorCylinder ratio function level,
      ∃ digit : Bool × Bool, level ∈ Set.Ioo
        (function (wordMap ratio (parent.word ++ [digit]) 0))
        (function (wordMap ratio (parent.word ++ [digit]) (1, 1))) := by
    intro parent
    have hscale : 0 < ratio ^ parent.word.length := pow_pos hpositive _
    obtain ⟨digit, hdigit⟩ := nonlinear_one_strict_child
      (growth.word_restriction hpositive hless parent.word) hpositive hhalf
      (by nlinarith [mul_lt_mul_of_pos_left houter hscale])
      (by nlinarith [mul_lt_mul_of_pos_left hmiddle hscale]) parent.interior_level
    exact ⟨digit, by simpa only [wordMap_append, Function.comp_apply] using hdigit⟩
  obtain ⟨point, hpoint, hpoint_level, hdeep⟩ := deep_interior_cylinders_of_child_cover
    hpositive hhalf hcontinuous hlevel hcover
  obtain ⟨scale, slope, hscale, bands, hderivative⟩ := hderivatives point hpoint
  obtain ⟨threshold, hthreshold, neighborhood, hopen, hcontains, hcriterion⟩ :=
    two_band_local_source_criterion ratio slope hpositive hhalf bands
  obtain ⟨margin, hmargin, hmargin_mem⟩ := open_interval_neighborhood_margin
    (show 1 - ratio ≤ slope + ratio by linarith [bands.1]) hopen hcontains
  let bound : ℝ≥0 := ⟨min threshold margin / 2, by positivity⟩
  have hbound_positive : 0 < bound := by change 0 < min threshold margin / 2; positivity
  have hbound_threshold : (bound : ℝ) < threshold := by
    change min threshold margin / 2 < threshold
    linarith [min_le_left threshold margin]
  have hbound_margin : (bound : ℝ) < margin := by
    change min threshold margin / 2 < margin
    linarith [min_le_right threshold margin]
  obtain ⟨minimumDepth, hsmall⟩ := strict_derivative_cylinder_error hpositive hless hderivative
    bound hbound_positive
  obtain ⟨parent, hdepth, hparent_point, hparent_level⟩ := hdeep minimumDepth
  have hparent_error := hsmall parent hdepth hparent_point
  have hparent_scale : 0 < ratio ^ parent.length := pow_pos hpositive _
  obtain ⟨rest, hcentral⟩ := nonlinear_central_word
    (growth.word_restriction hpositive hless parent)
    (hcontinuous.comp (continuous_wordMap ratio parent)) hpositive hhalf
    (mul_pos hparent_scale hlowerS) (mul_lt_mul_of_pos_left hslope hparent_scale)
    (by nlinarith [mul_lt_mul_of_pos_left hshell hparent_scale]) hparent_level
  let word := parent ++ rest
  have herror : LipschitzOnWith bound
      (fun value => function value / scale - positiveLinearContinuous slope value)
      (wordCylinder ratio word) :=
    hparent_error.mono (wordCylinder_append_subset hpositive.le hless parent rest)
  have hcentral_normalized : level / scale ∈ Set.Ioo
      (function (wordMap ratio word (1 - ratio, 0)) / scale)
      (function (wordMap ratio word (ratio, 1)) / scale) := by
    constructor
    · exact (div_lt_div_iff_of_pos_right hscale).mpr
        (by simpa only [word, wordMap_append, Function.comp_apply] using hcentral.1)
    · exact (div_lt_div_iff_of_pos_right hscale).mpr
        (by simpa only [word, wordMap_append, Function.comp_apply] using hcentral.2)
  have hcentral_first : (1 - ratio, (0 : ℝ)) ∈ cantorDust ratio := by
    convert wordMap_mem_dust hpositive.le hless [(true, false)]
      (show (0 : ℝ × ℝ) ∈ cantorDust ratio from ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩) using 1 <;>
      simp [wordMap, digitPoint]
  have hcentral_second : (ratio, (1 : ℝ)) ∈ cantorDust ratio := by
    convert wordMap_mem_dust hpositive.le hless [(false, true)]
      (show ((1 : ℝ), (1 : ℝ)) ∈ cantorDust ratio from
        ⟨one_mem_cantorSet hpositive.le hless, one_mem_cantorSet hpositive.le hless⟩) using 1 <;>
      ext <;> simp [wordMap, digitPoint] <;> ring
  have hfirst_error := normalized_corner_linear_error hpositive hless
    (fun value => function value / scale) (positiveLinearContinuous slope) word bound herror hcentral_first
  have hsecond_error := normalized_corner_linear_error hpositive hless
    (fun value => function value / scale) (positiveLinearContinuous slope) word bound herror hcentral_second
  simp [positiveLinearContinuous, positiveLinear] at hfirst_error hsecond_error
  have hnormalized_level : (level / scale - function (wordMap ratio word 0) / scale) /
      ratio ^ word.length ∈ neighborhood := by
    apply hmargin_mem
    · have hstrict := div_lt_div_of_pos_right
        (sub_lt_sub_right hcentral_normalized.1 (function (wordMap ratio word 0) / scale))
        (pow_pos hpositive word.length)
      linarith [(abs_le.mp hfirst_error).1, (abs_le.mp hfirst_error).2]
    · have hstrict := div_lt_div_of_pos_right
        (sub_lt_sub_right hcentral_normalized.2 (function (wordMap ratio word 0) / scale))
        (pow_pos hpositive word.length)
      linarith [(abs_le.mp hsecond_error).1, (abs_le.mp hsecond_error).2]
  have hdimension := hcriterion bound hbound_threshold (fun value => function value / scale)
    (level / scale) word herror hnormalized_level
  apply hdimension.trans_le (dimH_mono ?_)
  intro value hvalue
  exact ⟨hvalue.1, (div_left_inj' hscale.ne').mp hvalue.2⟩

end LambdaCantor.Last
