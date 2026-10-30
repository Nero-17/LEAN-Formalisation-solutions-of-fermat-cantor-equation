import LambdaCantor.Last.AnalyticIsolatedBoundaryShadow
import LambdaCantor.Last.AnalyticIsolatedOrbit

noncomputable section
namespace LambdaCantor.Last

theorem boundary_no033_of_error_margin {ratio : ℝ} (positive : 0 < ratio)
    (orbit : ℕ → ℝ) (digits : ℕ → Bool × Bool) (errors : ℕ → ℝ)
    (recurrence : ∀ depth, orbit depth = boundaryChildOffset ratio (digits depth)+ratio*orbit (depth+1))
    (exclusive : ∀ depth, BoundaryApproxExclusive ratio (orbit depth) (errors depth) (digits depth))
    (depth : ℕ)
    (margin : errors depth+ratio^2*errors (depth+2) < ratio*(2+ratio^2)-(1-ratio)) :
    ¬ (digits depth = (false,false) ∧ digits (depth+1) = (true,true) ∧
      digits (depth+2) = (true,true)) := by
  rintro ⟨first, second, third⟩
  have upper := exclusive depth
  have lower := exclusive (depth+2)
  rw [first] at upper
  rw [third] at lower
  change orbit depth ≤ 1-ratio+errors depth at upper
  change 1+2*ratio-errors (depth+2) ≤ orbit (depth+2) at lower
  have first_step := recurrence depth
  have second_step := recurrence (depth+1)
  rw [first] at first_step
  rw [second] at second_step
  simp only [boundaryChildOffset, Bool.false_eq_true, if_false, if_true,
    mul_zero, zero_add, add_zero, mul_one] at first_step second_step
  have combined : orbit depth = ratio*((1-ratio)*(2+ratio)+ratio*orbit (depth+2)) := by
    rw [first_step, second_step]
    ring
  have estimate : ratio*((1-ratio)*(2+ratio)+ratio*(1+2*ratio-errors (depth+2))) ≤ orbit depth := by
    rw [combined]
    gcongr
  nlinarith

theorem boundary_no300_of_error_margin {ratio : ℝ} (positive : 0 < ratio)
    (orbit : ℕ → ℝ) (digits : ℕ → Bool × Bool) (errors : ℕ → ℝ)
    (recurrence : ∀ depth, orbit depth = boundaryChildOffset ratio (digits depth)+ratio*orbit (depth+1))
    (exclusive : ∀ depth, BoundaryApproxExclusive ratio (orbit depth) (errors depth) (digits depth))
    (depth : ℕ)
    (margin : errors depth+ratio^2*errors (depth+2) < ratio*(2+ratio^2)-(1-ratio)) :
    ¬ (digits depth = (true,true) ∧ digits (depth+1) = (false,false) ∧
      digits (depth+2) = (false,false)) := by
  rintro ⟨first, second, third⟩
  have lower := exclusive depth
  have upper := exclusive (depth+2)
  rw [first] at lower
  rw [third] at upper
  change 1+2*ratio-errors depth ≤ orbit depth at lower
  change orbit (depth+2) ≤ 1-ratio+errors (depth+2) at upper
  have first_step := recurrence depth
  have second_step := recurrence (depth+1)
  rw [first] at first_step
  rw [second] at second_step
  simp only [boundaryChildOffset, Bool.false_eq_true, if_false, if_true,
    mul_zero, zero_add, add_zero, mul_one] at first_step second_step
  have combined : orbit depth = (1-ratio)*(2+ratio)+ratio*(ratio*orbit (depth+2)) := by
    rw [first_step, second_step]
    ring
  have estimate : orbit depth ≤ (1-ratio)*(2+ratio)+ratio*(ratio*(1-ratio+errors (depth+2))) := by
    rw [combined]
    gcongr
  nlinarith

theorem boundary_finitely_mixed_periodic {ratio coefficient : ℝ}
    (critical : ratio = (Real.sqrt 3-1)/2) (coefficient_positive : 0 < coefficient)
    (orbit : ℕ → ℝ) (digits : ℕ → Bool × Bool) (errors : ℕ → ℝ)
    (recurrence : ∀ depth, orbit depth = boundaryChildOffset ratio (digits depth)+ratio*orbit (depth+1))
    (exclusive : ∀ depth, BoundaryApproxExclusive ratio (orbit depth) (errors depth) (digits depth))
    (error_bound : ∀ depth, errors depth ≤ coefficient*ratio^depth)
    (mixed_finite : ∃ cutoff : ℕ, ∀ depth, cutoff ≤ depth →
      digits depth ≠ (true,false) ∧ digits depth ≠ (false,true)) :
    EventuallyPeriodicPairedAddress digits := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have ratio_positive : 0 < ratio := by rw [critical]; nlinarith
  have ratio_less_half : ratio < 1/2 := by rw [critical]; nlinarith
  have ratio_less_one : ratio < 1 := by linarith
  have margin_positive : 0 < ratio*(2+ratio^2)-(1-ratio) := by
    have lower : (1/3 : ℝ) < ratio := by rw [critical]; nlinarith
    nlinarith [pow_nonneg ratio_positive.le 3]
  obtain ⟨errorCutoff, error_small⟩ := exists_pow_lt_of_lt_one
    (div_pos margin_positive (mul_pos (by norm_num : (0 : ℝ) < 4) coefficient_positive)) ratio_less_one
  have errors_small : ∀ depth, errorCutoff ≤ depth →
      errors depth < (ratio*(2+ratio^2)-(1-ratio))/4 := by
    intro depth depth_lower
    have monotone := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one ratio_positive.le ratio_less_one.le depth_lower) coefficient_positive.le
    have small := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) coefficient_positive)).mp error_small
    nlinarith [error_bound depth]
  obtain ⟨mixedCutoff, no_mixed⟩ := mixed_finite
  let shift := max errorCutoff mixedCutoff
  have margins : ∀ index, errors (index+shift)+ratio^2*errors (index+shift+2) <
      ratio*(2+ratio^2)-(1-ratio) := by
    intro index
    have first_small := errors_small (index+shift) (by dsimp [shift]; omega)
    have second_small := errors_small (index+shift+2) (by dsimp [shift]; omega)
    have scaled := mul_le_mul_of_nonneg_left second_small.le (sq_nonneg ratio)
    have quarter_positive : 0 ≤ (ratio*(2+ratio^2)-(1-ratio))/4 := by positivity
    have contraction := mul_le_mul_of_nonneg_right
      (show ratio^2 ≤ 1 by nlinarith) quarter_positive
    nlinarith
  have periodic : EventuallyPeriodicPairedAddress (fun index => digits (index+shift)) := by
    apply paired_address_periodic_of_two_symbols_no_double_change
    · intro index
      have not_mixed := no_mixed (index+shift) (by dsimp [shift]; omega)
      have diagonal : ∀ digit : Bool × Bool,
          digit ≠ (true,false) ∧ digit ≠ (false,true) →
          digit = (false,false) ∨ digit = (true,true) := by decide
      exact diagonal (digits (index+shift)) not_mixed
    · intro index
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        boundary_no033_of_error_margin ratio_positive orbit digits errors recurrence exclusive
          (index+shift) (margins index)
    · intro index
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        boundary_no300_of_error_margin ratio_positive orbit digits errors recurrence exclusive
          (index+shift) (margins index)
  obtain ⟨prefixLength, period, period_positive, periodic⟩ := periodic
  refine ⟨shift+prefixLength, period, period_positive, ?_⟩
  intro index
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using periodic index

end LambdaCantor.Last
