import LambdaCantor.Last.AnalyticIsolatedAffine
import LambdaCantor.Last.ArithmeticAffineFibres
import LambdaCantor.Last.PerfectAffineReturns

noncomputable section
namespace LambdaCantor.Last

theorem open_phase_affine_fibre_two_points_uncountable {ratio slope level : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2) (slope_lower : 1 ≤ slope)
    (outer : 1-2*ratio < ratio*slope) (middle : (1-2*ratio)*slope < 1)
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope)
    (outside : slope ∉ parameterField ratio)
    {first second : ℝ × ℝ} (first_mem : first ∈ cantorDust ratio) (second_mem : second ∈ cantorDust ratio)
    (first_level : positiveLinear slope first = level) (second_level : positiveLinear slope second = level)
    (different : first ≠ second) :
    ¬ {value | value ∈ cantorDust ratio ∧ positiveLinear slope value = level}.Countable := by
  have compact : IsCompact {value | value ∈ cantorDust ratio ∧ positiveLinear slope value = level} :=
    (isCompact_cantorDust positive.le (by linarith)).inter_right
      (isClosed_eq (positiveLinearContinuous slope).continuous continuous_const)
  apply affine_fibre_two_points_uncountable_over_field (parameterField ratio) _ compact outside
    (fun _ membership => membership.2)
    (fun point isolated => isolated_affine_point_in_parameterField positive less_half slope_lower
      outer middle phase point isolated)
    (show first ∈ {value | value ∈ cantorDust ratio ∧ positiveLinear slope value = level} from
      ⟨first_mem, first_level⟩)
    (show second ∈ {value | value ∈ cantorDust ratio ∧ positiveLinear slope value = level} from
      ⟨second_mem, second_level⟩) different

theorem open_phase_affine_overlap_fibres_uncountable {ratio slope : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2) (slope_lower : 1 ≤ slope)
    (outer : 1-2*ratio < ratio*slope) (middle : (1-2*ratio)*slope < 1)
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope)
    (outside : slope ∉ parameterField ratio) :
    ∀ level ∈ affineOverlapCore ratio slope,
      ¬ {value | value ∈ cantorDust ratio ∧ positiveLinear slope value = level}.Countable := by
  intro level membership
  obtain ⟨firstDigit, secondDigit, different, first_hull, second_hull⟩ := mem_affineOverlapCore.mp membership
  have first_brackets : level ∈ Set.Icc
      (positiveLinearContinuous slope (wordMap ratio [firstDigit] 0))
      (positiveLinearContinuous slope (wordMap ratio [firstDigit] (1,1))) := by
    change level ∈ Set.Icc
      (positiveLinearContinuous slope (wordMap ratio [firstDigit] 0))
      (positiveLinearContinuous slope (wordMap ratio [firstDigit] 0)+ratio*(1+slope)) at first_hull
    rw [(affine_child_endpoint_values ratio slope firstDigit).2,
      ← (affine_child_endpoint_values ratio slope firstDigit).1]
    exact first_hull
  have second_brackets : level ∈ Set.Icc
      (positiveLinearContinuous slope (wordMap ratio [secondDigit] 0))
      (positiveLinearContinuous slope (wordMap ratio [secondDigit] (1,1))) := by
    change level ∈ Set.Icc
      (positiveLinearContinuous slope (wordMap ratio [secondDigit] 0))
      (positiveLinearContinuous slope (wordMap ratio [secondDigit] 0)+ratio*(1+slope)) at second_hull
    rw [(affine_child_endpoint_values ratio slope secondDigit).2,
      ← (affine_child_endpoint_values ratio slope secondDigit).1]
    exact second_hull
  obtain ⟨first, first_in_child, first_level⟩ := affine_closed_word_hull_filled
    positive less_half outer middle [firstDigit] first_brackets
  obtain ⟨second, second_in_child, second_level⟩ := affine_closed_word_hull_filled
    positive less_half outer middle [secondDigit] second_brackets
  have less_one : ratio < 1 := by linarith
  have first_mem := wordCylinder_subset_dust positive.le less_one [firstDigit] first_in_child
  have second_mem := wordCylinder_subset_dust positive.le less_one [secondDigit] second_in_child
  have points_different : first ≠ second := by
    obtain ⟨firstTail, first_tail_mem, first_representation⟩ := first_in_child
    obtain ⟨secondTail, second_tail_mem, second_representation⟩ := second_in_child
    have separated := first_digit_distance_gap positive.le less_one firstDigit secondDigit different
      first_tail_mem second_tail_mem
    rw [first_representation, second_representation] at separated
    intro equal
    rw [equal, dist_self] at separated
    linarith
  exact open_phase_affine_fibre_two_points_uncountable positive less_half slope_lower outer middle
    phase outside first_mem second_mem first_level second_level points_different

/-- The actual arithmetic/symbolic affine route supplies the complete return
input consumed by the parent's compact finite-return construction. -/
theorem open_phase_affine_overlap_strict_returns {ratio slope : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2) (slope_lower : 1 ≤ slope)
    (outer : 1-2*ratio < ratio*slope) (middle : (1-2*ratio)*slope < 1)
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope)
    (outside : slope ∉ parameterField ratio) :
    ∀ level ∈ affineOverlapCore ratio slope, ∃ pair : ReturnPair,
      linearWordReturn ratio (positiveLinear slope) (pair.word false) level ∈ interior (affineOverlapCore ratio slope) ∧
      linearWordReturn ratio (positiveLinear slope) (pair.word true) level ∈ interior (affineOverlapCore ratio slope) := by
  intro level membership
  exact affine_fibre_strict_returns_of_uncountable positive less_half (by linarith)
    (open_phase_affine_overlap_fibres_uncountable positive less_half slope_lower outer middle phase outside
      level membership)

end LambdaCantor.Last
