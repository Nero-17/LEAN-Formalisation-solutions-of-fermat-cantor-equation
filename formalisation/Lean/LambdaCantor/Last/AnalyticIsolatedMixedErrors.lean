import LambdaCantor.Last.AnalyticIsolatedApproximateOrbit

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

theorem paired_address_periodic_of_absorbing_mixed
    (digits : ℕ → Bool × Bool)
    (transitions : ∀ depth,
      (digits depth = (true,false) → digits (depth+1) = (true,false)) ∧
      (digits depth = (false,true) → digits (depth+1) = (false,true)) ∧
      (digits depth = (false,false) → digits (depth+1) ≠ (true,true)) ∧
      (digits depth = (true,true) → digits (depth+1) ≠ (false,false))) :
    EventuallyPeriodicPairedAddress digits := by
  classical
  by_cases mixed : ∃ prefixLength, digits prefixLength = (true,false) ∨ digits prefixLength = (false,true)
  · obtain ⟨prefixLength, first | second⟩ := mixed
    · have constant : ∀ index, digits (prefixLength+index) = (true,false) := by
        intro index
        induction index with
        | zero => simpa using first
        | succ index induction => exact (transitions (prefixLength+index)).1 induction
      refine ⟨prefixLength, 1, by decide, ?_⟩
      intro index
      rw [show index+prefixLength+1 = prefixLength+(index+1) by omega,
        show index+prefixLength = prefixLength+index by omega, constant, constant]
    · have constant : ∀ index, digits (prefixLength+index) = (false,true) := by
        intro index
        induction index with
        | zero => simpa using second
        | succ index induction => exact (transitions (prefixLength+index)).2.1 induction
      refine ⟨prefixLength, 1, by decide, ?_⟩
      intro index
      rw [show index+prefixLength+1 = prefixLength+(index+1) by omega,
        show index+prefixLength = prefixLength+index by omega, constant, constant]
  · push_neg at mixed
    refine ⟨0, 1, by decide, ?_⟩
    intro index
    have previous := mixed index
    have next := mixed (index+1)
    have step := transitions index
    rcases firstDigit : digits index with ⟨first, second⟩
    rcases secondDigit : digits (index+1) with ⟨nextFirst, nextSecond⟩
    cases first <;> cases second <;> cases nextFirst <;> cases nextSecond <;> simp_all

theorem mixed_phase_approx_transition {ratio slope level nextLevel error nextError : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2) (phase : MixedPeriodicityPhase ratio slope)
    (lower_margin : error+ratio*nextError < ratio*slope-(1-ratio-ratio^2))
    (upper_margin : error+ratio*nextError < 1-(1-ratio-ratio^2)*slope)
    (digit nextDigit : Bool × Bool)
    (exclusive : ApproxAffineExclusiveRegion ratio slope level error digit)
    (next_exclusive : ApproxAffineExclusiveRegion ratio slope nextLevel nextError nextDigit)
    (recurrence : level = affineChildOffset ratio slope digit+ratio*nextLevel) :
    (digit = (true,false) → nextDigit = (true,false)) ∧
    (digit = (false,true) → nextDigit = (false,true)) ∧
    (digit = (false,false) → nextDigit ≠ (true,true)) ∧
    (digit = (true,true) → nextDigit ≠ (false,false)) := by
  have slope_positive : 0 < slope := by linarith [phase.1]
  have reference_order : 0 ≤ ratio*((slope-1)*(1-ratio)) :=
    mul_nonneg positive.le (mul_nonneg (by linarith [phase.1]) (by linarith))
  rcases digit with ⟨first, second⟩
  rcases nextDigit with ⟨nextFirst, nextSecond⟩
  cases first <;> cases second <;> cases nextFirst <;> cases nextSecond <;>
    simp_all [ApproxAffineExclusiveRegion, affineChildOffset] <;>
    nlinarith [mul_pos positive slope_positive]

/-- The second open periodicity phase is stable under vanishing C¹ endpoint
errors. Mixed symbols become absorbing, and the two outer symbols cannot
switch directly; no constant mixed orbit is excluded in this classification. -/
theorem mixed_phase_approx_address_periodic {ratio slope : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2) (phase : MixedPeriodicityPhase ratio slope)
    (orbit : ℕ → ℝ) (digits : ℕ → Bool × Bool) (errors : ℕ → ℝ)
    (errors_zero : Tendsto errors atTop (𝓝 0))
    (exclusive : ∀ depth, ApproxAffineExclusiveRegion ratio slope (orbit depth) (errors depth) (digits depth))
    (recurrence : ∀ depth, orbit depth = affineChildOffset ratio slope (digits depth)+ratio*orbit (depth+1)) :
    EventuallyPeriodicPairedAddress digits := by
  have first_positive : 0 < ratio*slope-(1-ratio-ratio^2) := by linarith [phase.2.1]
  have second_positive : 0 < 1-(1-ratio-ratio^2)*slope := by linarith [phase.2.2]
  have tolerance_positive : 0 < min (ratio*slope-(1-ratio-ratio^2))
      (1-(1-ratio-ratio^2)*slope)/4 := by positivity
  obtain ⟨cutoff, errors_small⟩ := Filter.eventually_atTop.mp
    (errors_zero.eventually (gt_mem_nhds tolerance_positive))
  have margin : ∀ depth, cutoff ≤ depth →
      errors depth+ratio*errors (depth+1) < min (ratio*slope-(1-ratio-ratio^2))
        (1-(1-ratio-ratio^2)*slope) := by
    intro depth depth_lower
    have first_small := errors_small depth depth_lower
    have second_small := errors_small (depth+1) (by omega)
    have scaled := mul_le_mul_of_nonneg_left second_small.le positive.le
    have contraction := mul_le_mul_of_nonneg_right (show ratio ≤ 1 by linarith)
      (show 0 ≤ min (ratio*slope-(1-ratio-ratio^2)) (1-(1-ratio-ratio^2)*slope)/4 by positivity)
    nlinarith
  have periodic : EventuallyPeriodicPairedAddress (fun depth => digits (depth+cutoff)) := by
    apply paired_address_periodic_of_absorbing_mixed
    intro depth
    have errors_margin := margin (depth+cutoff) (by omega)
    have first_margin := errors_margin.trans_le (min_le_left _ _)
    have second_margin := errors_margin.trans_le (min_le_right _ _)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using mixed_phase_approx_transition
      positive less_half phase first_margin second_margin (digits (depth+cutoff))
        (digits (depth+cutoff+1)) (exclusive _) (exclusive _) (recurrence _)
  obtain ⟨prefixLength, period, period_positive, periodic⟩ := periodic
  refine ⟨cutoff+prefixLength, period, period_positive, ?_⟩
  intro index
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using periodic index

end LambdaCantor.Last
