import LambdaCantor.Last.AnalyticIsolatedOrbit
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

def ApproxAffineExclusiveRegion (ratio slope level error : ℝ) (digit : Bool × Bool) : Prop :=
  match digit with
  | (false,false) => level ≤ 1-ratio+error
  | (true,false) => ratio*(1+slope)-error ≤ level ∧ level ≤ slope*(1-ratio)+error
  | (false,true) => 1+ratio*slope-error ≤ level ∧ level ≤ (1-ratio)*(1+slope)+error
  | (true,true) => ratio+slope-error ≤ level

theorem small_phase_approx_no_mixed {ratio slope level error : ℝ}
    (small_error : 2*error < ratio-(1-2*ratio)*slope) {digit : Bool × Bool}
    (exclusive : ApproxAffineExclusiveRegion ratio slope level error digit) :
    digit = (false,false) ∨ digit = (true,true) := by
  rcases digit with ⟨first, second⟩
  cases first <;> cases second <;> simp_all [ApproxAffineExclusiveRegion] <;> nlinarith

theorem small_phase_approx_no033 {ratio slope : ℝ} (positive : 0 < ratio)
    (orbit : ℕ → ℝ) (digits : ℕ → Bool × Bool) (errors : ℕ → ℝ)
    (exclusive : ∀ depth, ApproxAffineExclusiveRegion ratio slope (orbit depth) (errors depth) (digits depth))
    (recurrence : ∀ depth, orbit depth = affineChildOffset ratio slope (digits depth)+ratio*orbit (depth+1))
    (depth : ℕ)
    (margin : errors depth+ratio^2*errors (depth+2) <
      ratio*(1-ratio+ratio^2+slope)-(1-ratio)) :
    ¬ (digits depth = (false,false) ∧ digits (depth+1) = (true,true) ∧ digits (depth+2) = (true,true)) := by
  rintro ⟨first, second, third⟩
  have upper := exclusive depth
  have lower := exclusive (depth+2)
  rw [first] at upper
  rw [third] at lower
  change orbit depth ≤ 1-ratio+errors depth at upper
  change ratio+slope-errors (depth+2) ≤ orbit (depth+2) at lower
  have first_step := recurrence depth
  have second_step := recurrence (depth+1)
  rw [first] at first_step
  rw [second] at second_step
  simp only [affineChildOffset, Bool.false_eq_true, if_false, if_true,
    mul_zero, zero_add, add_zero, mul_one] at first_step second_step
  have combined : orbit depth = ratio*((1-ratio)*(1+slope)+ratio*orbit (depth+2)) := by
    rw [first_step, second_step]
  have estimate : ratio*((1-ratio)*(1+slope)+ratio*(ratio+slope-errors (depth+2))) ≤ orbit depth := by
    rw [combined]
    gcongr
  nlinarith

theorem small_phase_approx_no300 {ratio slope : ℝ} (positive : 0 < ratio)
    (orbit : ℕ → ℝ) (digits : ℕ → Bool × Bool) (errors : ℕ → ℝ)
    (exclusive : ∀ depth, ApproxAffineExclusiveRegion ratio slope (orbit depth) (errors depth) (digits depth))
    (recurrence : ∀ depth, orbit depth = affineChildOffset ratio slope (digits depth)+ratio*orbit (depth+1))
    (depth : ℕ)
    (margin : errors depth+ratio^2*errors (depth+2) <
      ratio*(1-ratio+ratio^2+slope)-(1-ratio)) :
    ¬ (digits depth = (true,true) ∧ digits (depth+1) = (false,false) ∧ digits (depth+2) = (false,false)) := by
  rintro ⟨first, second, third⟩
  have lower := exclusive depth
  have upper := exclusive (depth+2)
  rw [first] at lower
  rw [third] at upper
  change ratio+slope-errors depth ≤ orbit depth at lower
  change orbit (depth+2) ≤ 1-ratio+errors (depth+2) at upper
  have first_step := recurrence depth
  have second_step := recurrence (depth+1)
  rw [first] at first_step
  rw [second] at second_step
  simp only [affineChildOffset, Bool.false_eq_true, if_false, if_true,
    mul_zero, zero_add, add_zero, mul_one] at first_step second_step
  have combined : orbit depth = (1-ratio)*(1+slope)+ratio*(ratio*orbit (depth+2)) := by
    rw [first_step, second_step]
  have estimate : orbit depth ≤ (1-ratio)*(1+slope)+ratio*(ratio*(1-ratio+errors (depth+2))) := by
    rw [combined]
    gcongr
  nlinarith

/-- The first open phase is stable under all vanishing C¹ endpoint errors.
The conclusion includes the tangent ratio one; no separation of the two mixed
affine hulls is needed by the symbolic argument itself. -/
theorem small_phase_approx_address_periodic {ratio slope : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2) (phase : SmallPeriodicityPhase ratio slope)
    (orbit : ℕ → ℝ) (digits : ℕ → Bool × Bool) (errors : ℕ → ℝ)
    (errors_zero : Tendsto errors atTop (𝓝 0))
    (exclusive : ∀ depth, ApproxAffineExclusiveRegion ratio slope (orbit depth) (errors depth) (digits depth))
    (recurrence : ∀ depth, orbit depth = affineChildOffset ratio slope (digits depth)+ratio*orbit (depth+1)) :
    EventuallyPeriodicPairedAddress digits := by
  have mixed_margin : 0 < ratio-(1-2*ratio)*slope := by linarith [phase.2.1]
  have triple_margin : 0 < ratio*(1-ratio+ratio^2+slope)-(1-ratio) := by linarith [phase.2.2]
  have tolerance_positive : 0 < min (ratio-(1-2*ratio)*slope)
      (ratio*(1-ratio+ratio^2+slope)-(1-ratio))/4 := by positivity
  obtain ⟨cutoff, errors_small⟩ := Filter.eventually_atTop.mp
    (errors_zero.eventually (gt_mem_nhds tolerance_positive))
  have mixed_errors : ∀ depth, cutoff ≤ depth → 2*errors depth < ratio-(1-2*ratio)*slope := by
    intro depth depth_lower
    have small := errors_small depth depth_lower
    linarith [min_le_left (ratio-(1-2*ratio)*slope)
      (ratio*(1-ratio+ratio^2+slope)-(1-ratio))]
  have triple_errors : ∀ depth, cutoff ≤ depth → errors depth+ratio^2*errors (depth+2) <
      ratio*(1-ratio+ratio^2+slope)-(1-ratio) := by
    intro depth depth_lower
    have first_small := errors_small depth depth_lower
    have second_small := errors_small (depth+2) (by omega)
    have minimum_upper := min_le_right (ratio-(1-2*ratio)*slope)
      (ratio*(1-ratio+ratio^2+slope)-(1-ratio))
    have second_upper : errors (depth+2) ≤ (ratio*(1-ratio+ratio^2+slope)-(1-ratio))/4 := by linarith
    have scaled := mul_le_mul_of_nonneg_left second_upper (sq_nonneg ratio)
    have quarter_nonnegative : 0 ≤ (ratio*(1-ratio+ratio^2+slope)-(1-ratio))/4 := by positivity
    have contraction := mul_le_mul_of_nonneg_right (show ratio^2 ≤ 1 by nlinarith) quarter_nonnegative
    nlinarith
  have periodic : EventuallyPeriodicPairedAddress (fun depth => digits (depth+cutoff)) := by
    apply paired_address_periodic_of_two_symbols_no_double_change
    · intro depth
      exact small_phase_approx_no_mixed (mixed_errors (depth+cutoff) (by omega)) (exclusive _)
    · intro depth
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        small_phase_approx_no033 positive orbit digits errors exclusive recurrence (depth+cutoff)
          (triple_errors _ (by omega))
    · intro depth
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        small_phase_approx_no300 positive orbit digits errors exclusive recurrence (depth+cutoff)
          (triple_errors _ (by omega))
  obtain ⟨prefixLength, period, period_positive, periodic⟩ := periodic
  refine ⟨cutoff+prefixLength, period, period_positive, ?_⟩
  intro index
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using periodic index

end LambdaCantor.Last
