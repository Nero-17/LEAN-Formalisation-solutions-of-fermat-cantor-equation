import LambdaCantor.Circle.RootFibreData
import LambdaCantor.Circle.ZeroIntervalSequence
import LambdaCantor.Circle.ZeroParameterConsequences

noncomputable section
open Filter MeasureTheory
namespace LambdaCantor.Circle
open LambdaCantor.First.Roots

theorem circle_expectedDimension_positive {ratio : ℝ}
    (above_quarter : 1 / 4 < ratio) (below_half : ratio < 1 / 2) :
    0 < expectedDimension ratio := by
  have positive : 0 < ratio := by linarith
  have reciprocal_above_one : 1 < 1 / ratio := (lt_div_iff₀ positive).mpr (by linarith)
  have reciprocal_below_four : 1 / ratio < (2 : ℝ) ^ 2 :=
    (div_lt_iff₀ positive).mpr (by nlinarith)
  have logarithm_positive := Real.log_pos reciprocal_above_one
  have logarithm_bound := Real.log_lt_log (div_pos (by norm_num) positive) reciprocal_below_four
  rw [Real.log_pow] at logarithm_bound
  have quotient_above_one : 1 < 2 * Real.log 2 / Real.log (1 / ratio) :=
    (lt_div_iff₀ logarithm_positive).mpr (by simpa using logarithm_bound)
  unfold expectedDimension
  linarith

/-- The final measure-theoretic deduction uses the actual root-fibre
conclusion and the concrete circle data. No measurability assertion about
the set of dimensions is needed, since Lebesgue measure is an outer measure. -/
theorem circle_positive_measure_of_rootFibreConclusion
    (root_fibres : ∀ data : RootFibreData 2, RootFibreConclusion data)
    (epsilon : ℝ) (epsilon_positive : 0 < epsilon) :
    0 < volume {ratio : ℝ | ratio ∈ Set.Ioo onset (onset + epsilon) ∧
      0 < dimH (intersection 2 ratio)} := by
  obtain ⟨power, power_small⟩ : ∃ power : ℕ, (7 / 25 : ℝ) ^ power < epsilon / 2 :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  have power_bound := power_antitone (by norm_num : (0 : ℝ) ≤ 7 / 25)
    (by norm_num : (7 / 25 : ℝ) ≤ 1) (show power ≤ 2 * (power + 2) + 1 by omega)
  obtain ⟨data, root_eq, lower_above, upper_near⟩ := circle_rootFibreData_exists (power + 2) (by omega)
  have upper_epsilon : data.upper < onset + epsilon := by linarith
  have conclusion := root_fibres data
  letI := rootFibreData_rootLaw_probability data
  have in_band : ∀ᵐ ratio ∂rootLaw data.root, ratio ∈ Set.Icc data.lower data.upper := by
    apply (ae_mem_iff_measure_eq measurableSet_Icc.nullMeasurableSet).mpr
    simpa using rootFibreData_rootLaw_parameter_band data
  have positive_parameters : ∀ᵐ ratio ∂rootLaw data.root,
      ratio ∈ Set.Ioo onset (onset + epsilon) ∧ 0 < dimH (intersection 2 ratio) := by
    apply (in_band.and conclusion.2).mono
    rintro ratio ⟨parameter_band, dimension⟩
    refine ⟨⟨lower_above.trans_le parameter_band.1, parameter_band.2.trans_lt upper_epsilon⟩, ?_⟩
    rw [dimension]
    exact ENNReal.ofReal_pos.mpr (circle_expectedDimension_positive
      (data.lower_gt_quarter.trans_le parameter_band.1)
      (parameter_band.2.trans_lt data.upper_lt_half))
  apply pos_iff_ne_zero.mpr
  intro zero
  have zero_root := conclusion.1 zero
  have almost_not := measure_eq_zero_iff_ae_notMem.mp zero_root
  obtain ⟨ratio, member, not_member⟩ := (positive_parameters.and almost_not).exists
  exact not_member member

theorem circle_onset_of_positive_parameters
    (positive_parameters : ∀ epsilon : ℝ, 0 < epsilon →
      0 < volume {ratio : ℝ | ratio ∈ Set.Ioo onset (onset + epsilon) ∧
        0 < dimH (intersection 2 ratio)}) : firstTransition 2 = onset := by
  have parameter_exists (epsilon : ℝ) (epsilon_positive : 0 < epsilon) :
      ∃ ratio ∈ Set.Ioo onset (onset + epsilon), 0 < dimH (intersection 2 ratio) := by
    exact nonempty_of_measure_ne_zero (ne_of_gt (positive_parameters epsilon epsilon_positive))
  have gap_positive : 0 < (1 / 2 : ℝ) - onset := by linarith [onset_lt_one_third]
  obtain ⟨ratio, bounds, dimension⟩ := parameter_exists _ gap_positive
  have nonempty_parameters : {ratio : ℝ | ratio ∈ Set.Ioc (0 : ℝ) (1 / 2) ∧
      0 < dimH (intersection 2 ratio)}.Nonempty :=
    ⟨ratio, ⟨onset_pos.trans bounds.1, by linarith [bounds.2]⟩, dimension⟩
  apply le_antisymm
  · by_contra contrary
    have epsilon_positive : 0 < (firstTransition 2 - onset) / 2 := by
      have := lt_of_not_ge contrary
      linarith
    obtain ⟨ratio, bounds, dimension⟩ := parameter_exists
      (min ((firstTransition 2 - onset) / 2) ((1 / 2 : ℝ) - onset))
      (lt_min epsilon_positive gap_positive)
    have admissible : ratio ∈ Set.Ioc (0 : ℝ) (1 / 2) := by
      have := min_le_right ((firstTransition 2 - onset) / 2) ((1 / 2 : ℝ) - onset)
      exact ⟨onset_pos.trans bounds.1, by linarith [bounds.2]⟩
    have := min_le_left ((firstTransition 2 - onset) / 2) ((1 / 2 : ℝ) - onset)
    have := firstTransition_le_of_positive admissible dimension
    linarith [bounds.2]
  · exact onset_le_firstTransition nonempty_parameters

theorem circle_onset_of_rootFibreConclusion
    (root_fibres : ∀ data : RootFibreData 2, RootFibreConclusion data) :
    firstTransition 2 = onset :=
  circle_onset_of_positive_parameters (circle_positive_measure_of_rootFibreConclusion root_fibres)

theorem circle_known_separation_of_rootFibreConclusion
    (root_fibres : ∀ data : RootFibreData 2, RootFibreConclusion data) :
    firstTransition 2 = onset ∧ onset < lastTransition 2 :=
  ⟨circle_onset_of_rootFibreConclusion root_fibres, onset_lt_lastTransition⟩

end LambdaCantor.Circle
