import LambdaCantor.Last.AnalyticIsolatedActualOpen
import LambdaCantor.Last.AnalyticIsolatedActualBoundary

noncomputable section
namespace LambdaCantor.Last

theorem open_phase_isolated_c2_point_in_parameterField {ratio slope : ℝ}
    (above_third : (1/3 : ℝ) < ratio) (less_half : ratio < 1/2)
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope)
    (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (point : {value | value ∈ cantorDust ratio ∧ function value = level})
    (isolated : IsOpen ({point} : Set {value | value ∈ cantorDust ratio ∧ function value = level}))
    (smooth : ContDiffAt ℝ 2 function point.val)
    (derivative : HasFDerivAt function (positiveLinearContinuous slope) point.val) :
    point.val.1 ∈ parameterField ratio ∧ point.val.2 ∈ parameterField ratio := by
  obtain ⟨firstDigits, first_address⟩ := point.property.1.1
  obtain ⟨secondDigits, second_address⟩ := point.property.1.2
  apply open_phase_isolated_c2_address_in_parameterField above_third less_half phase function level point isolated
    (fun index => (firstDigits index, secondDigits index)) _ smooth derivative
  apply Prod.ext
  · simpa [pairedAddressTail] using first_address.symm
  · simpa [pairedAddressTail] using second_address.symm

theorem critical_isolated_c2_point_in_parameterField {ratio : ℝ}
    (critical : ratio = (Real.sqrt 3-1)/2)
    (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (point : {value | value ∈ cantorDust ratio ∧ function value = level})
    (isolated : IsOpen ({point} : Set {value | value ∈ cantorDust ratio ∧ function value = level}))
    (smooth : ContDiffAt ℝ 2 function point.val)
    (derivative : HasFDerivAt function (positiveLinearContinuous (1+ratio)) point.val)
    (first_algebraic : IsAlgebraic ℚ point.val.1) (second_algebraic : IsAlgebraic ℚ point.val.2) :
    point.val.1 ∈ parameterField ratio ∧ point.val.2 ∈ parameterField ratio := by
  obtain ⟨firstDigits, first_address⟩ := point.property.1.1
  obtain ⟨secondDigits, second_address⟩ := point.property.1.2
  apply critical_isolated_c2_address_in_parameterField critical function level point isolated
    (fun index => (firstDigits index, secondDigits index)) _ smooth derivative first_algebraic second_algebraic
  apply Prod.ext
  · simpa [pairedAddressTail] using first_address.symm
  · simpa [pairedAddressTail] using second_address.symm

end LambdaCantor.Last
