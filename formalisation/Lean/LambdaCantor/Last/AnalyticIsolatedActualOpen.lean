import LambdaCantor.Last.AnalyticIsolatedActualOpenCylinder
import LambdaCantor.Last.AnalyticIsolatedMixedErrors
import LambdaCantor.Last.AnalyticIsolatedQuadraticError

noncomputable section
open scoped NNReal
open Filter
open scoped Topology
namespace LambdaCantor.Last

/-- Actual C² isolated-address classification in both open periodicity
phases. The use of C² is sufficient for all positive rational Fermat arcs;
the symbolic stability lemmas themselves only require vanishing C¹ errors. -/
theorem open_phase_isolated_c2_address_in_parameterField {ratio slope : ℝ}
    (above_third : (1/3 : ℝ) < ratio) (less_half : ratio < 1/2)
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope)
    (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (point : {value | value ∈ cantorDust ratio ∧ function value = level})
    (isolated : IsOpen ({point} : Set {value | value ∈ cantorDust ratio ∧ function value = level}))
    (digits : ℕ → Bool × Bool) (address_point : point.val = pairedAddressTail ratio digits 0)
    (smooth : ContDiffAt ℝ 2 function point.val)
    (derivative : HasFDerivAt function (positiveLinearContinuous slope) point.val) :
    point.val.1 ∈ parameterField ratio ∧ point.val.2 ∈ parameterField ratio := by
  have positive : 0 < ratio := by linarith
  have less_one : ratio < 1 := by linarith
  obtain ⟨coefficient, coefficient_positive, errorCutoff, cylinder_errors⟩ :=
    c2_derivative_cylinder_error positive less_one smooth derivative
  obtain ⟨isolationCutoff, singleton⟩ := isolated_fibre_eventually_singleton_cylinders
    positive less_half function level point isolated
  obtain ⟨toleranceCutoff, tolerances⟩ := eventually_actualPhaseTolerance
    (coefficient := (coefficient : ℝ)) above_third less_half phase
  let shift := max isolationCutoff (max errorCutoff toleranceCutoff)
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
      ApproxAffineExclusiveRegion ratio slope
        (positiveLinearContinuous slope (pairedAddressTail ratio digits (index+shift)))
        (2*(coefficient : ℝ)*ratio^(index+shift)) (digits (index+shift)) := by
    intro index
    let bound : ℝ≥0 := coefficient * NNReal.mk (ratio ^ (index + shift)) (pow_nonneg positive.le _)
    have tolerance : ActualPhaseTolerance ratio slope bound :=
      tolerances (index+shift) (by dsimp [shift]; omega)
    have lipschitz := cylinder_errors (pairedAddressPrefix digits (index+shift))
      (by rw [pairedAddressPrefix_length]; dsimp [shift]; omega) (point_in_word _)
    rw [pairedAddressPrefix_length] at lipschitz
    have normalized_error : ∀ value ∈ cantorDust ratio,
        |normalizedActualFunction function ratio (pairedAddressPrefix digits (index+shift)) value-
          positiveLinearContinuous slope value| ≤ bound := by
      intro value value_mem
      exact normalized_actual_error_of_cylinder_lipschitz positive less_one function _ lipschitz value_mem
    have single : ∀ other : ℝ × ℝ, other ∈ cantorDust ratio → function other = function point.val →
        other ∈ wordCylinder ratio (pairedAddressPrefix digits (index+shift)) → other = point.val := by
      intro other other_mem other_level other_word
      exact singleton _ (by rw [pairedAddressPrefix_length]; dsimp [shift]; omega)
        (point_in_word _) other other_mem (other_level.trans point.property.2) other_word
    have result := actual_open_phase_cylinder_exclusive positive less_half
      function (pairedAddressPrefix digits (index+shift)) point.val tolerance lipschitz normalized_error single
      (digits (index+shift)) (pairedAddressTail ratio digits ((index+shift)+1))
      (pairedAddressTail_mem_dust ratio digits _) (representation _)
    rw [← pairedAddressTail_recurrence positive.le less_one digits (index+shift)] at result
    simpa only [bound, NNReal.coe_mul, NNReal.coe_mk, mul_assoc] using result
  have errors_zero : Tendsto (fun depth : ℕ => 2*(coefficient : ℝ)*ratio^(depth+shift)) atTop (𝓝 0) := by
    simpa [pow_add, mul_assoc, mul_comm, mul_left_comm] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one positive.le less_one).mul_const
        (2*(coefficient : ℝ)*ratio^shift))
  have recurrence : ∀ depth,
      positiveLinearContinuous slope (pairedAddressTail ratio digits (depth+shift)) =
        affineChildOffset ratio slope (digits (depth+shift))+ratio*
          positiveLinearContinuous slope (pairedAddressTail ratio digits ((depth+1)+shift)) := by
    intro depth
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      pairedAddressTail_affine_orbit positive.le less_one slope digits (depth+shift)
  have shifted_periodic : EventuallyPeriodicPairedAddress (fun depth => digits (depth+shift)) := by
    rcases phase with small | mixed
    · exact small_phase_approx_address_periodic positive less_half small _ _ _ errors_zero actual_exclusive recurrence
    · exact mixed_phase_approx_address_periodic positive less_half mixed _ _ _ errors_zero actual_exclusive recurrence
  obtain ⟨prefixLength, period, period_positive, periodic⟩ := shifted_periodic
  have periodic_original : EventuallyPeriodicPairedAddress digits := by
    refine ⟨shift+prefixLength, period, period_positive, ?_⟩
    intro index
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using periodic index
  have fields := paired_periodic_coordinates_in_parameterField positive.le less_one periodic_original
  simpa [address_point, pairedAddressTail] using fields

end LambdaCantor.Last
