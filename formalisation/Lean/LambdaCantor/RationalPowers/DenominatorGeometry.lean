import LambdaCantor.RationalPowers.DenominatorCover
import LambdaCantor.Integer.LogBounds
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

noncomputable section
namespace LambdaCantor.RationalPowers

/-- An elementary strict logarithmic lower bound, valid at every positive
real endpoint rather than just the finite certificate endpoints. -/
theorem log_one_add_inverse_gt (endpoint : ℝ) (positive : 0 < endpoint) :
    1/(endpoint+1) < Real.log (1+1/endpoint) := by
  have logarithm := Real.lt_log_one_add_of_pos (one_div_pos.mpr positive)
  have rational_identity : 2*(1/endpoint)/(1/endpoint+2) = 2/(1+2*endpoint) := by
    field_simp [positive.ne']
    <;> ring
  have rational_bound : 1/(endpoint+1) < 2*(1/endpoint)/(1/endpoint+2) := by
    rw [rational_identity]
    apply (div_lt_div_iff₀ (by positivity : 0 < endpoint+1) (by positivity : 0 < 1+2*endpoint)).mpr
    linarith
  exact rational_bound.trans logarithm

theorem log_three_lt_eleven_tenths : Real.log 3 < 11/10 := by
  have bound := (Integer.log_series_bounds 3 (by norm_num) 5).2
  norm_num [Integer.logSeriesUpper, Integer.logSeriesLower, Finset.sum_range_succ] at bound
  linarith

/-- Appending horizontal zero digits preserves the certified full derivative
band and the uniform logarithmic-width lower bound at every real exponent in
the scaled source interval. -/
theorem scaled_denominator_source (normalized scale : ℝ)
    (normalized_lower : 1 ≤ normalized) (normalized_upper : normalized ≤ 3)
    (scale_lower : 1 ≤ scale) :
    ∃ index : Fin 16,
      let source := denominatorSources index
      source.Checked ∧
      (source.lowerSlope : ℝ) < (scale*normalized)*source.vertical/(scale*source.horizontal+1) ∧
      (scale*normalized)*(source.vertical+1)/(scale*source.horizontal) < (source.upperSlope : ℝ) ∧
      11/1100 < (scale*normalized)*Real.log (1+1/(scale*source.horizontal))+
        Real.log (1+1/(source.vertical : ℝ)) := by
  obtain ⟨index, checked, lower, upper, width⟩ :=
    normalized_denominator_source normalized normalized_lower normalized_upper
  have horizontal_positive : (0 : ℝ) < (denominatorSources index).horizontal := by
    exact_mod_cast checked.1
  have vertical_positive : (0 : ℝ) < (denominatorSources index).vertical := by
    exact_mod_cast checked.2.1
  have lowerSlope_positive : (0 : ℝ) < (denominatorSources index).lowerSlope := by
    exact_mod_cast checked.2.2.2.2.2.2.1
  have scale_positive : 0 < scale := lt_of_lt_of_le zero_lt_one scale_lower
  have normalized_positive : 0 < normalized := lt_of_lt_of_le zero_lt_one normalized_lower
  have lower_cleared :
      ((denominatorSources index).lowerSlope : ℝ)*((denominatorSources index).horizontal+1) <
        normalized*(denominatorSources index).vertical :=
    (div_lt_iff₀ vertical_positive).mp lower
  have upper_cleared :
      normalized*((denominatorSources index).vertical+1) <
        ((denominatorSources index).upperSlope : ℝ)*(denominatorSources index).horizontal := by
    have result := (lt_div_iff₀ (by positivity : (0 : ℝ) <
      (denominatorSources index).vertical+1)).mp upper
    nlinarith
  have log_horizontal := log_one_add_inverse_gt (scale*(denominatorSources index).horizontal)
    (mul_pos scale_positive horizontal_positive)
  have log_vertical := log_one_add_inverse_gt ((denominatorSources index).vertical : ℝ) vertical_positive
  have first_width :
      normalized/((denominatorSources index).horizontal+1) ≤
        (scale*normalized)/(scale*(denominatorSources index).horizontal+1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg normalized_positive.le (sub_nonneg.mpr scale_lower)]
  have log_width :
      normalized/((denominatorSources index).horizontal+1) <
        (scale*normalized)*Real.log (1+1/(scale*(denominatorSources index).horizontal)) := by
    have multiplied := mul_lt_mul_of_pos_left log_horizontal (mul_pos scale_positive normalized_positive)
    rw [mul_one_div] at multiplied
    exact first_width.trans_lt multiplied
  refine ⟨index, checked, ?_, ?_, ?_⟩
  · apply (lt_div_iff₀ (by positivity : (0 : ℝ) <
      scale*(denominatorSources index).horizontal+1)).mpr
    nlinarith [mul_pos scale_positive (sub_pos.mpr lower_cleared),
      mul_nonneg lowerSlope_positive.le (sub_nonneg.mpr scale_lower)]
  · apply (div_lt_iff₀ (by positivity : (0 : ℝ) <
      scale*(denominatorSources index).horizontal)).mpr
    nlinarith [mul_pos scale_positive (sub_pos.mpr upper_cleared)]
  · have direct_width : 11/1100 < normalized/((denominatorSources index).horizontal+1)+
        1/((denominatorSources index).vertical+1) := by
      have cleared := (lt_div_iff₀ (by positivity : (0 : ℝ) <
        (denominatorSources index).horizontal+1)).mpr width
      linarith
    linarith

/-- Every real interval wider than the phase lattice spacing contains a
strict interior lattice point. Both corner inequalities therefore remain strict. -/
theorem phase_lattice_point (denominator : ℕ) (positive : 0 < denominator)
    (lower upper : ℝ) (width : 1/(denominator : ℝ) < upper-lower) :
    ∃ phase : ℤ, lower < (phase : ℝ)/denominator ∧
      (phase : ℝ)/denominator < upper := by
  have denominator_positive : (0 : ℝ) < denominator := by exact_mod_cast positive
  refine ⟨⌊(denominator : ℝ)*lower⌋+1, ?_, ?_⟩
  · apply (lt_div_iff₀ denominator_positive).mpr
    simpa only [Int.cast_add, Int.cast_one, mul_comm] using
      Int.lt_floor_add_one ((denominator : ℝ)*lower)
  · apply (div_lt_iff₀ denominator_positive).mpr
    have floor_lower := Int.floor_le ((denominator : ℝ)*lower)
    have cleared := (div_lt_iff₀ denominator_positive).mp width
    push_cast
    nlinarith

/-- The cutoff 110 is justified using a proved logarithm enclosure and the
strict width estimate, rather than a floating-point comparison. -/
theorem denominator_width_exceeds_spacing (denominator : ℕ) (cutoff : 110 ≤ denominator)
    (width : ℝ) (wide : 11/1100 < width) :
    1/(denominator : ℝ) < width/Real.log 3 := by
  have denominator_lower : (110 : ℝ) ≤ denominator := by exact_mod_cast cutoff
  have logarithm_positive : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have logarithm_upper := log_three_lt_eleven_tenths
  have denominator_positive : (0 : ℝ) < denominator := by linarith
  apply (div_lt_div_iff₀ denominator_positive logarithm_positive).mpr
  nlinarith [mul_le_mul_of_nonneg_left denominator_lower (show 0 ≤ width by linarith)]

/-- Denominator-dependent version used by the inexpensive width-covered
part of the low-denominator finite partition. -/
theorem positive_width_exceeds_spacing (denominator : ℕ) (positive : 0 < denominator)
    (width : ℝ) (wide : 11/(10*(denominator : ℝ)) < width) :
    1/(denominator : ℝ) < width/Real.log 3 := by
  have denominator_positive : (0 : ℝ) < denominator := by exact_mod_cast positive
  have logarithm_positive : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have cleared := (div_lt_iff₀ (by positivity : (0 : ℝ) < 10*(denominator : ℝ))).mp wide
  apply (div_lt_div_iff₀ denominator_positive logarithm_positive).mpr
  nlinarith [log_three_lt_eleven_tenths]

end LambdaCantor.RationalPowers

