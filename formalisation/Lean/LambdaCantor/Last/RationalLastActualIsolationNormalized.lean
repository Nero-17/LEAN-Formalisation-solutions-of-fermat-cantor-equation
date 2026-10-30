import LambdaCantor.Last.RationalLastNormalizationExchange
import LambdaCantor.Last.RationalLastActualIsolationPhases
import LambdaCantor.Last.AnalyticIsolatedActualPoints

noncomputable section
namespace LambdaCantor.Last

/-- Normalized actual C² classification at c. The algebraicity input is
needed only at the two exact boundary slopes. The Fermat specialization
derives this input from its actual rational equation. -/
theorem critical_normalized_c2_isolated_coordinates_mem_parameterField {ratio slope : ℝ}
    (critical : ratio = (Real.sqrt 3-1)/2) (normalized : 1 ≤ slope ∧ slope < 1/ratio)
    (function : (ℝ × ℝ) → ℝ)
    (point : {value | value ∈ cantorDust ratio ∧ function value = 0})
    (isolated : IsOpen ({point} : Set {value | value ∈ cantorDust ratio ∧ function value = 0}))
    (smooth : ContDiffAt ℝ 2 function point.val)
    (derivative : HasStrictFDerivAt function (positiveLinearContinuous slope) point.val)
    (boundary_algebraic : slope = 1+ratio ∨ slope = 2 →
      IsAlgebraic ℚ point.val.1 ∧ IsAlgebraic ℚ point.val.2) :
    point.val.1 ∈ parameterField ratio ∧ point.val.2 ∈ parameterField ratio := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have ratio_positive : 0 < ratio := by rw [critical]; nlinarith
  have above_third : (1/3 : ℝ) < ratio := by rw [critical]; nlinarith
  have less_half : ratio < 1/2 := by rw [critical]; nlinarith
  have less_one : ratio < 1 := by linarith
  have slope_positive : 0 < slope := by linarith [normalized.1]
  have exchanged_classification : SmallPeriodicityPhase ratio (1/(ratio*slope)) ∨ slope = 2 →
      point.val.1 ∈ parameterField ratio ∧ point.val.2 ∈ parameterField ratio := by
    intro exchanged_phase
    obtain ⟨digit, preimage, preimage_mem, representation⟩ :=
      exists_prefixExchange_preimage ratio_positive.le less_one point.property.1
    have zero : exchangedNormalizedFunction ratio slope digit function preimage = 0 := by
      unfold exchangedNormalizedFunction
      rw [representation, point.property.2]
      simp
    let exchangedPoint : {value | value ∈ cantorDust ratio ∧
        exchangedNormalizedFunction ratio slope digit function value = 0} :=
      ⟨preimage, preimage_mem, zero⟩
    have exchanged_isolated := exchangedNormalizedFunction_isolated_pullback ratio_positive less_one
      slope_positive digit function point exchangedPoint representation isolated
    have exchanged_smooth := exchangedNormalizedFunction_contDiffAt (ratio := ratio) (slope := slope) digit function
      (point := preimage) (by rw [representation]; exact smooth)
    have exchanged_derivative := exchangedNormalizedFunction_hasStrictFDerivAt ratio_positive slope_positive
      digit function (point := preimage) (by rw [representation]; exact derivative)
    have fields : preimage.1 ∈ parameterField ratio ∧ preimage.2 ∈ parameterField ratio := by
      rcases exchanged_phase with open_phase | second_boundary
      · exact open_phase_isolated_c2_point_in_parameterField above_third less_half (Or.inl open_phase)
          (exchangedNormalizedFunction ratio slope digit function) 0 exchangedPoint exchanged_isolated
          exchanged_smooth exchanged_derivative.hasFDerivAt
      · have algebraic := boundary_algebraic (Or.inr second_boundary)
        have preimage_algebraic := prefixExchangeMap_preimage_algebraic ratio_positive
          (critical_ratio_algebraic critical) digit representation algebraic.1 algebraic.2
        apply critical_isolated_c2_point_in_parameterField critical
          (exchangedNormalizedFunction ratio slope digit function) 0 exchangedPoint exchanged_isolated
          exchanged_smooth _ preimage_algebraic.1 preimage_algebraic.2
        simpa only [second_boundary, critical_inverse_two_phase critical] using
          exchanged_derivative.hasFDerivAt
    have mapped_fields := prefixExchangeMap_coordinates_mem_parameterField digit fields.1 fields.2
    rw [representation] at mapped_fields
    exact mapped_fields
  rcases critical_normalized_isolation_phase_cases critical normalized with
    small | mixed | exchanged_small | first_boundary | second_boundary
  · exact open_phase_isolated_c2_point_in_parameterField above_third less_half (Or.inl small)
      function 0 point isolated smooth derivative.hasFDerivAt
  · exact open_phase_isolated_c2_point_in_parameterField above_third less_half (Or.inr mixed)
      function 0 point isolated smooth derivative.hasFDerivAt
  · exact exchanged_classification (Or.inl exchanged_small)
  · have algebraic := boundary_algebraic (Or.inl first_boundary)
    apply critical_isolated_c2_point_in_parameterField critical function 0 point isolated smooth
      _ algebraic.1 algebraic.2
    simpa only [first_boundary] using derivative.hasFDerivAt
  · exact exchanged_classification (Or.inr second_boundary)

end LambdaCantor.Last
