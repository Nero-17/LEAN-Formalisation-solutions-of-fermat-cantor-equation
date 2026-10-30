import LambdaCantor.Last.AnalyticIsolatedActualBoundaryCylinder
import LambdaCantor.Last.AnalyticIsolatedBoundaryClassification
import LambdaCantor.Last.AnalyticIsolatedAddresses
import LambdaCantor.Last.AnalyticIsolatedActualError
import LambdaCantor.Last.AnalyticIsolatedQuadraticError
import LambdaCantor.Last.ArithmeticAlgebraicField

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

/-- Actual critical-phase C² isolation classification. Every input concerns
the actual function, actual relative fibre isolation, actual binary addresses,
or coordinate algebraicity. The proof constructs the endpoint-error models,
unique closed children, shadowing blocks, and digit-theorem hypotheses; none
of those paper-internal conclusions is an assumption of this theorem. -/
theorem critical_isolated_c2_address_in_parameterField {ratio : ℝ}
    (critical : ratio = (Real.sqrt 3-1)/2)
    (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (point : {value | value ∈ cantorDust ratio ∧ function value = level})
    (isolated : IsOpen ({point} : Set {value | value ∈ cantorDust ratio ∧ function value = level}))
    (digits : ℕ → Bool × Bool) (address_point : point.val = pairedAddressTail ratio digits 0)
    (smooth : ContDiffAt ℝ 2 function point.val)
    (derivative : HasFDerivAt function (positiveLinearContinuous (1+ratio)) point.val)
    (first_algebraic : IsAlgebraic ℚ point.val.1) (second_algebraic : IsAlgebraic ℚ point.val.2) :
    point.val.1 ∈ parameterField ratio ∧ point.val.2 ∈ parameterField ratio := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have positive : 0 < ratio := by rw [critical]; nlinarith
  have less_half : ratio < 1/2 := by rw [critical]; nlinarith
  have less_one : ratio < 1 := by linarith
  have ratio_lower : (1/3 : ℝ) < ratio := by rw [critical]; nlinarith
  have critical_equation : 2*ratio^2+2*ratio=1 := by rw [critical]; nlinarith
  obtain ⟨coefficient, coefficient_positive, errorCutoff, cylinder_errors⟩ :=
    c2_derivative_cylinder_error positive less_one smooth derivative
  obtain ⟨isolationCutoff, singleton⟩ := isolated_fibre_eventually_singleton_cylinders
    positive less_half function level point isolated
  obtain ⟨smallCutoff, scale_small⟩ := exists_pow_lt_of_lt_one
    (div_pos (by norm_num : (0 : ℝ) < 1/100) (show (0 : ℝ) < coefficient from coefficient_positive)) less_one
  let shift := max isolationCutoff (max errorCutoff smallCutoff)
  have point_in_word : ∀ depth, point.val ∈ wordCylinder ratio (pairedAddressPrefix digits depth) := by
    intro depth
    exact ⟨pairedAddressTail ratio digits depth, pairedAddressTail_mem_dust ratio digits depth,
      (pairedAddressPrefix_representation positive.le less_one digits depth).trans address_point.symm⟩
  have representation : ∀ depth,
      wordMap ratio (pairedAddressPrefix digits depth)
        (wordMap ratio [digits depth] (pairedAddressTail ratio digits (depth+1))) = point.val := by
    intro depth
    rw [← pairedAddressTail_recurrence positive.le less_one digits depth]
    exact (pairedAddressPrefix_representation positive.le less_one digits depth).trans address_point.symm
  have actual_exclusive : ∀ index,
      BoundaryApproxExclusive ratio
        (positiveLinearContinuous (1+ratio) (pairedAddressTail ratio digits (index+shift)))
        (2*(coefficient : ℝ)*ratio^(index+shift)) (digits (index+shift)) := by
    intro index
    let bound : ℝ≥0 := coefficient * NNReal.mk (ratio ^ (index + shift)) (pow_nonneg positive.le _)
    have small_bound : (bound : ℝ) ≤ 1/100 := by
      have monotone := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one positive.le less_one.le (show smallCutoff ≤ index+shift by dsimp [shift]; omega))
        coefficient.coe_nonneg
      have small := (lt_div_iff₀ (show (0 : ℝ) < coefficient from coefficient_positive)).mp scale_small
      change (coefficient : ℝ)*ratio^(index+shift) ≤ 1/100
      nlinarith
    have lipschitz := cylinder_errors (pairedAddressPrefix digits (index+shift))
      (by rw [pairedAddressPrefix_length]; dsimp [shift]; omega) (point_in_word _)
    rw [pairedAddressPrefix_length] at lipschitz
    have normalized_error : ∀ value ∈ cantorDust ratio,
        |normalizedActualFunction function ratio (pairedAddressPrefix digits (index+shift)) value-
          positiveLinearContinuous (1+ratio) value| ≤ bound := by
      intro value value_mem
      exact normalized_actual_error_of_cylinder_lipschitz positive less_one function _ lipschitz value_mem
    have single : ∀ other : ℝ × ℝ, other ∈ cantorDust ratio → function other = function point.val →
        other ∈ wordCylinder ratio (pairedAddressPrefix digits (index+shift)) → other = point.val := by
      intro other other_mem other_level other_word
      exact singleton _ (by rw [pairedAddressPrefix_length]; dsimp [shift]; omega)
        (point_in_word _) other other_mem (other_level.trans point.property.2) other_word
    have result := actual_boundary_cylinder_exclusive positive less_half critical_equation ratio_lower
      function (pairedAddressPrefix digits (index+shift)) point.val small_bound lipschitz normalized_error single
      (digits (index+shift)) (pairedAddressTail ratio digits ((index+shift)+1))
      (pairedAddressTail_mem_dust ratio digits _) (representation _)
    rw [← pairedAddressTail_recurrence positive.le less_one digits (index+shift)] at result
    simpa only [bound, NNReal.coe_mul, NNReal.coe_mk, mul_assoc] using result
  have first_eq : point.val.1 = address ratio (fun index => (digits index).1) := by
    simpa [pairedAddressTail] using congrArg Prod.fst address_point
  have second_eq : point.val.2 = address ratio (fun index => (digits index).2) := by
    simpa [pairedAddressTail] using congrArg Prod.snd address_point
  have first_address_algebraic : IsAlgebraic ℚ (address ratio (fun index => (digits index).1)) :=
    first_eq ▸ first_algebraic
  have second_address_algebraic : IsAlgebraic ℚ (address ratio (fun index => (digits index).2)) :=
    second_eq ▸ second_algebraic
  have shifted_fields := boundary_exclusive_orbit_coordinates_in_field
    (coefficient := 2*(coefficient : ℝ)*ratio^shift) critical (by positivity)
    (fun index => positiveLinearContinuous (1+ratio) (pairedAddressTail ratio digits (index+shift)))
    (fun index => digits (index+shift)) (fun index => 2*(coefficient : ℝ)*ratio^(index+shift))
    (fun depth => by
      simpa [positiveLinearContinuous, positiveLinear, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        pairedAddressTail_boundary_orbit positive.le less_one digits (depth+shift))
    actual_exclusive
    (fun depth => by rw [pow_add]; apply le_of_eq; ring)
    (address_tail_algebraic positive less_one (critical_ratio_algebraic critical) _ first_address_algebraic shift)
    (address_tail_algebraic positive less_one (critical_ratio_algebraic critical) _ second_address_algebraic shift)
  constructor
  · rw [first_eq]
    exact address_mem_parameterField_of_tail positive.le less_one _ shift shifted_fields.1
  · rw [second_eq]
    exact address_mem_parameterField_of_tail positive.le less_one _ shift shifted_fields.2

end LambdaCantor.Last
