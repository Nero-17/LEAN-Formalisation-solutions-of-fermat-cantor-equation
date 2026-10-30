import LambdaCantor.Last.RationalLastNormalizationExchange
import LambdaCantor.Last.AnalyticIsolatedPhaseCoverage
import LambdaCantor.Last.AnalyticIsolatedActualPoints
import LambdaCantor.Last.RationalLastArithmeticIsolation

noncomputable section
namespace LambdaCantor.Last

theorem above_critical_normalized_c2_isolated_coordinates_mem_parameterField {ratio slope : ℝ}
    (above_critical : (Real.sqrt 3-1)/2 < ratio) (less_half : ratio < 1/2)
    (normalized : 1 ≤ slope ∧ slope < 1/ratio)
    (function : (ℝ × ℝ) → ℝ)
    (point : {value | value ∈ cantorDust ratio ∧ function value = 0})
    (isolated : IsOpen ({point} : Set {value | value ∈ cantorDust ratio ∧ function value = 0}))
    (smooth : ContDiffAt ℝ 2 function point.val)
    (derivative : HasStrictFDerivAt function (positiveLinearContinuous slope) point.val) :
    point.val.1 ∈ parameterField ratio ∧ point.val.2 ∈ parameterField ratio := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have positive : 0 < ratio := by nlinarith
  have above_third : (1/3 : ℝ) < ratio := by nlinarith
  have less_one : ratio < 1 := by linarith
  rcases above_critical_normalized_phase_cases above_critical less_half normalized with small | mixed | exchanged
  · exact open_phase_isolated_c2_point_in_parameterField above_third less_half (Or.inl small)
      function 0 point isolated smooth derivative.hasFDerivAt
  · exact open_phase_isolated_c2_point_in_parameterField above_third less_half (Or.inr mixed)
      function 0 point isolated smooth derivative.hasFDerivAt
  · obtain ⟨digit, preimage, preimage_mem, representation⟩ :=
      exists_prefixExchange_preimage positive.le less_one point.property.1
    have zero : exchangedNormalizedFunction ratio slope digit function preimage = 0 := by
      unfold exchangedNormalizedFunction
      rw [representation, point.property.2]
      simp
    let exchangedPoint : {value | value ∈ cantorDust ratio ∧
        exchangedNormalizedFunction ratio slope digit function value = 0} :=
      ⟨preimage, preimage_mem, zero⟩
    have slope_positive : 0 < slope := by linarith [normalized.1]
    have exchanged_isolated := exchangedNormalizedFunction_isolated_pullback positive less_one
      slope_positive digit function point exchangedPoint representation isolated
    have exchanged_smooth := exchangedNormalizedFunction_contDiffAt (ratio := ratio) (slope := slope) digit function
      (point := preimage) (by rw [representation]; exact smooth)
    have exchanged_derivative := exchangedNormalizedFunction_hasStrictFDerivAt positive slope_positive
      digit function (point := preimage) (by rw [representation]; exact derivative)
    have fields := open_phase_isolated_c2_point_in_parameterField above_third less_half (Or.inl exchanged)
      (exchangedNormalizedFunction ratio slope digit function) 0 exchangedPoint exchanged_isolated
      exchanged_smooth exchanged_derivative.hasFDerivAt
    have mapped_fields := prefixExchangeMap_coordinates_mem_parameterField digit fields.1 fields.2
    rw [representation] at mapped_fields
    exact mapped_fields

/-- Above c, actual isolated-coordinate classification needs no rationality,
coordinate algebraicity, or digit theorem hypothesis. -/
theorem actual_fermat_isolated_coordinates_above_critical {exponent ratio : ℝ}
    (exponent_gt_one : 1 < exponent) (above_critical : (Real.sqrt 3-1)/2 < ratio)
    (less_half : ratio < 1/2) (point : intersection exponent ratio)
    (isolated : IsOpen ({point} : Set (intersection exponent ratio)))
    (first_positive : 0 < point.val.1) (second_positive : 0 < point.val.2) :
    point.val.1 ∈ parameterField ratio ∧ point.val.2 ∈ parameterField ratio := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have positive : 0 < ratio := by nlinarith
  have less_one : ratio < 1 := by linarith
  obtain ⟨firstWord, secondWord, tail, slope, height, tail_mem, representation, slope_identity,
      slope_lower, slope_upper, height_positive, zero, smooth, derivative⟩ :=
    exists_actual_fermat_prefix_normalization exponent_gt_one positive less_one point first_positive second_positive
  let normalizedPoint : {value | value ∈ cantorDust ratio ∧
      normalizedFermatPrefix exponent ratio firstWord secondWord height value = 0} := ⟨tail, tail_mem, zero⟩
  have normalized_isolated := normalizedFermatPrefix_isolated_pullback positive less_one
    height_positive.ne' firstWord secondWord point normalizedPoint representation isolated
  have fields := above_critical_normalized_c2_isolated_coordinates_mem_parameterField above_critical less_half
    ⟨slope_lower, slope_upper⟩ (normalizedFermatPrefix exponent ratio firstWord secondWord height)
    normalizedPoint normalized_isolated smooth derivative
  have mapped_fields := anisotropicPrefixMap_coordinates_mem_parameterField firstWord secondWord fields.1 fields.2
  rw [representation] at mapped_fields
  exact mapped_fields

theorem finite_isolated_actual_rational_intersection_above_critical
    {numerator denominator : ℕ} (numerator_large : 4 ≤ numerator)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    (exponent_gt_one : denominator < numerator) {ratio : ℝ}
    (above_critical : (Real.sqrt 3-1)/2 < ratio) (less_half : ratio < 1/2) :
    (isolatedPoints (intersection ((numerator : ℝ)/denominator) ratio)).Finite := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have positive : 0 < ratio := by nlinarith
  have less_one : ratio < 1 := by linarith
  have rational_exponent_gt_one : 1 < (numerator : ℝ)/denominator :=
    (one_lt_div (show (0 : ℝ) < denominator by exact_mod_cast denominator_positive)).mpr
      (by exact_mod_cast exponent_gt_one)
  apply finite_isolated_rational_intersection numerator_large denominator_positive coprime positive.le less_one
  intro point isolated first_positive second_positive
  exact actual_fermat_isolated_coordinates_above_critical rational_exponent_gt_one above_critical less_half
    point isolated first_positive second_positive

end LambdaCantor.Last
