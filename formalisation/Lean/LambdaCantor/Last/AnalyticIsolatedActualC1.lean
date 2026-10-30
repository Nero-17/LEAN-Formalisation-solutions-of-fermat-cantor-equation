import LambdaCantor.Last.AnalyticIsolatedActualOpenCylinder
import LambdaCantor.Last.AnalyticIsolatedMixedErrors
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open Filter
open scoped NNReal Topology
namespace LambdaCantor.Last

private def openPhaseUniformWordTolerance (ratio slope bound : ℝ) : Prop :=
  (SmallPeriodicityPhase ratio slope ∧
    4*bound < ratio-(1-2*ratio)*slope ∧
    2*bound+ratio^2*(2*bound) < ratio*(1-ratio+ratio^2+slope)-(1-ratio)) ∨
  (MixedPeriodicityPhase ratio slope ∧
    2*bound+ratio*(2*bound) < ratio*slope-(1-ratio-ratio^2) ∧
    2*bound+ratio*(2*bound) < 1-(1-ratio-ratio^2)*slope)

private theorem openPhaseUniformWordTolerance_near_zero {ratio slope : ℝ}
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope) :
    ∀ᶠ bound : ℝ in 𝓝 0, openPhaseUniformWordTolerance ratio slope bound := by
  rcases phase with small | mixed
  · have mixed_margin : ∀ᶠ bound : ℝ in 𝓝 0,
        4*bound < ratio-(1-2*ratio)*slope :=
      (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simpa using sub_pos.mpr small.2.1)
    have triple_margin : ∀ᶠ bound : ℝ in 𝓝 0,
        2*bound+ratio^2*(2*bound) < ratio*(1-ratio+ratio^2+slope)-(1-ratio) :=
      (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simpa using sub_pos.mpr small.2.2)
    filter_upwards [mixed_margin, triple_margin] with bound mixed_bound triple_bound
    exact Or.inl ⟨small, mixed_bound, triple_bound⟩
  · have lower_margin : ∀ᶠ bound : ℝ in 𝓝 0,
        2*bound+ratio*(2*bound) < ratio*slope-(1-ratio-ratio^2) :=
      (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simpa using sub_pos.mpr mixed.2.1)
    have upper_margin : ∀ᶠ bound : ℝ in 𝓝 0,
        2*bound+ratio*(2*bound) < 1-(1-ratio-ratio^2)*slope :=
      (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simpa using sub_pos.mpr mixed.2.2)
    filter_upwards [lower_margin, upper_margin] with bound lower_bound upper_bound
    exact Or.inr ⟨mixed, lower_bound, upper_bound⟩

/-- The open-phase address classification only needs strict differentiability.
One fixed sufficiently small cylinder error gives all finite word exclusions;
no C² bound, exponential rate, or stammering argument is needed. -/
theorem open_phase_isolated_strict_address_eventually_periodic {ratio slope : ℝ}
    (above_third : (1/3 : ℝ) < ratio) (less_half : ratio < 1/2)
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope)
    (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (point : {value | value ∈ cantorDust ratio ∧ function value = level})
    (isolated : IsOpen ({point} : Set {value | value ∈ cantorDust ratio ∧ function value = level}))
    (digits : ℕ → Bool × Bool) (address_point : point.val = pairedAddressTail ratio digits 0)
    (derivative : HasStrictFDerivAt function (positiveLinearContinuous slope) point.val) :
    EventuallyPeriodicPairedAddress digits := by
  have positive : 0 < ratio := by linarith
  have less_one : ratio < 1 := by linarith
  have tolerances_near := (actualPhaseTolerance_near_zero above_third less_half phase).and
    (openPhaseUniformWordTolerance_near_zero phase)
  obtain ⟨radius, radius_positive, ball_tolerance⟩ := Metric.mem_nhds_iff.mp tolerances_near
  let bound : ℝ≥0 := ⟨radius/2, by positivity⟩
  have bound_positive : 0 < bound := by change 0 < radius/2; positivity
  have tolerances : ActualPhaseTolerance ratio slope bound ∧
      openPhaseUniformWordTolerance ratio slope bound := by
    apply ball_tolerance
    apply Metric.mem_ball.mpr
    change dist (radius/2) 0 < radius
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos radius_positive)]
    linarith
  obtain ⟨errorCutoff, cylinder_errors⟩ :=
    strict_derivative_cylinder_error positive less_one derivative bound bound_positive
  obtain ⟨isolationCutoff, singleton⟩ := isolated_fibre_eventually_singleton_cylinders
    positive less_half function level point isolated
  let shift := max isolationCutoff errorCutoff
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
  have exclusive : ∀ index, ApproxAffineExclusiveRegion ratio slope
      (positiveLinearContinuous slope (pairedAddressTail ratio digits (index+shift)))
      (2*(bound : ℝ)) (digits (index+shift)) := by
    intro index
    have lipschitz := cylinder_errors (pairedAddressPrefix digits (index+shift))
      (by rw [pairedAddressPrefix_length]; dsimp [shift]; omega) (point_in_word _)
    have normalized_error : ∀ value ∈ cantorDust ratio,
        |normalizedActualFunction function ratio (pairedAddressPrefix digits (index+shift)) value-
          positiveLinearContinuous slope value| ≤ bound := by
      intro value membership
      exact normalized_actual_error_of_cylinder_lipschitz positive less_one function _ lipschitz membership
    have single : ∀ other : ℝ × ℝ, other ∈ cantorDust ratio → function other = function point.val →
        other ∈ wordCylinder ratio (pairedAddressPrefix digits (index+shift)) → other = point.val := by
      intro other other_mem other_level other_word
      exact singleton _ (by rw [pairedAddressPrefix_length]; dsimp [shift]; omega)
        (point_in_word _) other other_mem (other_level.trans point.property.2) other_word
    have result := actual_open_phase_cylinder_exclusive positive less_half function
      (pairedAddressPrefix digits (index+shift)) point.val tolerances.1 lipschitz normalized_error single
      (digits (index+shift)) (pairedAddressTail ratio digits ((index+shift)+1))
      (pairedAddressTail_mem_dust ratio digits _) (representation _)
    rw [← pairedAddressTail_recurrence positive.le less_one digits (index+shift)] at result
    exact result
  have recurrence : ∀ depth,
      positiveLinearContinuous slope (pairedAddressTail ratio digits (depth+shift)) =
        affineChildOffset ratio slope (digits (depth+shift))+ratio*
          positiveLinearContinuous slope (pairedAddressTail ratio digits ((depth+1)+shift)) := by
    intro depth
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      pairedAddressTail_affine_orbit positive.le less_one slope digits (depth+shift)
  have shifted_periodic : EventuallyPeriodicPairedAddress (fun depth => digits (depth+shift)) := by
    rcases tolerances.2 with small | mixed
    · apply paired_address_periodic_of_two_symbols_no_double_change
      · intro depth
        apply small_phase_approx_no_mixed _ (exclusive depth)
        linarith [small.2.1]
      · intro depth
        exact small_phase_approx_no033 positive _ _ (fun _ => 2*(bound : ℝ)) exclusive recurrence depth small.2.2
      · intro depth
        exact small_phase_approx_no300 positive _ _ (fun _ => 2*(bound : ℝ)) exclusive recurrence depth small.2.2
    · apply paired_address_periodic_of_absorbing_mixed
      intro depth
      exact mixed_phase_approx_transition positive less_half mixed.1 mixed.2.1 mixed.2.2
        (digits (depth+shift)) (digits ((depth+1)+shift)) (exclusive depth) (exclusive (depth+1)) (recurrence depth)
  obtain ⟨prefixLength, period, period_positive, periodic⟩ := shifted_periodic
  refine ⟨shift+prefixLength, period, period_positive, ?_⟩
  intro index
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using periodic index

theorem open_phase_isolated_strict_address_in_parameterField {ratio slope : ℝ}
    (above_third : (1/3 : ℝ) < ratio) (less_half : ratio < 1/2)
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope)
    (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (point : {value | value ∈ cantorDust ratio ∧ function value = level})
    (isolated : IsOpen ({point} : Set {value | value ∈ cantorDust ratio ∧ function value = level}))
    (digits : ℕ → Bool × Bool) (address_point : point.val = pairedAddressTail ratio digits 0)
    (derivative : HasStrictFDerivAt function (positiveLinearContinuous slope) point.val) :
    point.val.1 ∈ parameterField ratio ∧ point.val.2 ∈ parameterField ratio := by
  have periodic := open_phase_isolated_strict_address_eventually_periodic above_third less_half phase
    function level point isolated digits address_point derivative
  have fields := paired_periodic_coordinates_in_parameterField (show 0 ≤ ratio by linarith)
    (show ratio < 1 by linarith) periodic
  simpa [address_point, pairedAddressTail] using fields

theorem open_phase_isolated_c1_point_in_parameterField {ratio slope : ℝ}
    (above_third : (1/3 : ℝ) < ratio) (less_half : ratio < 1/2)
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope)
    (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (point : {value | value ∈ cantorDust ratio ∧ function value = level})
    (isolated : IsOpen ({point} : Set {value | value ∈ cantorDust ratio ∧ function value = level}))
    (smooth : ContDiffAt ℝ 1 function point.val)
    (derivative : HasFDerivAt function (positiveLinearContinuous slope) point.val) :
    point.val.1 ∈ parameterField ratio ∧ point.val.2 ∈ parameterField ratio := by
  obtain ⟨firstDigits, first_address⟩ := point.property.1.1
  obtain ⟨secondDigits, second_address⟩ := point.property.1.2
  apply open_phase_isolated_strict_address_in_parameterField above_third less_half phase function level point isolated
    (fun index => (firstDigits index, secondDigits index)) _
    (smooth.hasStrictFDerivAt' derivative (by norm_num))
  apply Prod.ext
  · simpa [pairedAddressTail] using first_address.symm
  · simpa [pairedAddressTail] using second_address.symm

end LambdaCantor.Last
