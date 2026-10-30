import LambdaCantor.Last.TwoBandOrbit
import LambdaCantor.Last.AnalyticIsolatedPeriodic

noncomputable section
namespace LambdaCantor.Last

def EventuallyPeriodicPairedAddress (digits : ℕ → Bool × Bool) : Prop :=
  ∃ prefixLength period : ℕ, 0 < period ∧
    ∀ index, digits (index+prefixLength+period) = digits (index+prefixLength)

/-- The first open interval in the isolated-address classification, expressed
as precisely the two strict comparisons used by the symbolic proof. -/
def SmallPeriodicityPhase (ratio slope : ℝ) : Prop :=
  1 ≤ slope ∧ (1-2*ratio)*slope < ratio ∧
    1-ratio < ratio*(1-ratio+ratio^2+slope)

/-- The second open interval retains both mixed fixed addresses, rather than
excluding them as in the narrower two-band positive-dimension lemma. -/
def MixedPeriodicityPhase (ratio slope : ℝ) : Prop :=
  1 < slope ∧ 1-ratio-ratio^2 < ratio*slope ∧ (1-ratio-ratio^2)*slope < 1

theorem small_phase_no_mixed {ratio slope level : ℝ}
    (phase : SmallPeriodicityPhase ratio slope) {digit : Bool × Bool}
    (exclusive : AffineExclusiveRegion ratio slope level digit) :
    digit = (false,false) ∨ digit = (true,true) := by
  rcases digit with ⟨first, second⟩
  cases first <;> cases second <;> simp_all [AffineExclusiveRegion]
  all_goals nlinarith [phase.2.1]

theorem small_phase_no_033 {ratio slope : ℝ} (positive : 0 < ratio)
    (phase : SmallPeriodicityPhase ratio slope) (orbit : ℕ → ℝ)
    (digits : ℕ → Bool × Bool)
    (exclusive : ∀ depth, AffineExclusiveRegion ratio slope (orbit depth) (digits depth))
    (recurrence : ∀ depth,
      orbit depth = affineChildOffset ratio slope (digits depth) + ratio*orbit (depth+1))
    (depth : ℕ) :
    ¬ (digits depth = (false,false) ∧ digits (depth+1) = (true,true) ∧
      digits (depth+2) = (true,true)) := by
  rintro ⟨first, second, third⟩
  have initial_bound := exclusive depth
  have final_bound := exclusive (depth+2)
  rw [first] at initial_bound
  rw [third] at final_bound
  change orbit depth ≤ 1-ratio at initial_bound
  change ratio+slope ≤ orbit (depth+2) at final_bound
  have first_recurrence := recurrence depth
  have second_recurrence := recurrence (depth+1)
  rw [first] at first_recurrence
  rw [second] at second_recurrence
  simp only [affineChildOffset, Bool.false_eq_true, if_false, if_true,
    zero_add, mul_zero, mul_one, add_zero] at first_recurrence second_recurrence
  have combined : orbit depth =
      ratio*((1-ratio)*(1+slope)+ratio*orbit (depth+2)) := by
    rw [first_recurrence, second_recurrence]
  have bound : ratio*((1-ratio)*(1+slope)+ratio*(ratio+slope)) ≤ orbit depth := by
    rw [combined]
    gcongr
  nlinarith [phase.2.2]

theorem small_phase_no_300 {ratio slope : ℝ} (positive : 0 < ratio)
    (phase : SmallPeriodicityPhase ratio slope) (orbit : ℕ → ℝ)
    (digits : ℕ → Bool × Bool)
    (exclusive : ∀ depth, AffineExclusiveRegion ratio slope (orbit depth) (digits depth))
    (recurrence : ∀ depth,
      orbit depth = affineChildOffset ratio slope (digits depth) + ratio*orbit (depth+1))
    (depth : ℕ) :
    ¬ (digits depth = (true,true) ∧ digits (depth+1) = (false,false) ∧
      digits (depth+2) = (false,false)) := by
  rintro ⟨first, second, third⟩
  have initial_bound := exclusive depth
  have final_bound := exclusive (depth+2)
  rw [first] at initial_bound
  rw [third] at final_bound
  change ratio+slope ≤ orbit depth at initial_bound
  change orbit (depth+2) ≤ 1-ratio at final_bound
  have first_recurrence := recurrence depth
  have second_recurrence := recurrence (depth+1)
  rw [first] at first_recurrence
  rw [second] at second_recurrence
  simp only [affineChildOffset, Bool.false_eq_true, if_false, if_true,
    zero_add, mul_zero, mul_one, add_zero] at first_recurrence second_recurrence
  have combined : orbit depth =
      (1-ratio)*(1+slope)+ratio*(ratio*orbit (depth+2)) := by
    rw [first_recurrence, second_recurrence]
  have bound : orbit depth ≤ (1-ratio)*(1+slope)+ratio*(ratio*(1-ratio)) := by
    rw [combined]
    gcongr
  nlinarith [phase.2.2]

theorem paired_address_periodic_of_two_symbols_no_double_change
    (digits : ℕ → Bool × Bool)
    (symbols : ∀ depth, digits depth = (false,false) ∨ digits depth = (true,true))
    (no033 : ∀ depth, ¬ (digits depth = (false,false) ∧
      digits (depth+1) = (true,true) ∧ digits (depth+2) = (true,true)))
    (no300 : ∀ depth, ¬ (digits depth = (true,true) ∧
      digits (depth+1) = (false,false) ∧ digits (depth+2) = (false,false))) :
    EventuallyPeriodicPairedAddress digits := by
  classical
  by_cases changes : ∃ depth, digits depth ≠ digits (depth+1)
  · obtain ⟨prefixLength, change⟩ := changes
    have alternating : ∀ index,
        digits (prefixLength+index) ≠ digits (prefixLength+index+1) ∧
          digits (prefixLength+index+2) = digits (prefixLength+index) := by
      intro index
      induction index with
      | zero =>
        have first := symbols prefixLength
        have second := symbols (prefixLength+1)
        have third := symbols (prefixLength+2)
        have forbidFirst := no033 prefixLength
        have forbidSecond := no300 prefixLength
        simp only [Nat.add_zero]
        rcases first with first | first <;> rcases second with second | second <;>
          rcases third with third | third <;> simp_all
      | succ index induction =>
        have first := symbols (prefixLength+index+1)
        have second := symbols (prefixLength+index+2)
        have third := symbols (prefixLength+index+3)
        have forbidFirst := no033 (prefixLength+index+1)
        have forbidSecond := no300 (prefixLength+index+1)
        have next_change : digits (prefixLength+index+1) ≠ digits (prefixLength+index+2) := by
          rw [induction.2]
          exact Ne.symm induction.1
        simp only [Nat.add_assoc] at *
        rcases first with first | first <;> rcases second with second | second <;>
          rcases third with third | third <;> simp_all
    refine ⟨prefixLength, 2, by decide, ?_⟩
    intro index
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (alternating index).2
  · push_neg at changes
    refine ⟨0, 1, by decide, ?_⟩
    intro index
    simpa using (changes index).symm

theorem small_phase_exclusive_address_periodic {ratio slope : ℝ}
    (positive : 0 < ratio) (phase : SmallPeriodicityPhase ratio slope)
    (orbit : ℕ → ℝ) (digits : ℕ → Bool × Bool)
    (exclusive : ∀ depth, AffineExclusiveRegion ratio slope (orbit depth) (digits depth))
    (recurrence : ∀ depth,
      orbit depth = affineChildOffset ratio slope (digits depth) + ratio*orbit (depth+1)) :
    EventuallyPeriodicPairedAddress digits :=
  paired_address_periodic_of_two_symbols_no_double_change digits
    (fun depth => small_phase_no_mixed phase (exclusive depth))
    (small_phase_no_033 positive phase orbit digits exclusive recurrence)
    (small_phase_no_300 positive phase orbit digits exclusive recurrence)

theorem mixed_phase_exclusive_transition {ratio slope level nextLevel : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2)
    (phase : MixedPeriodicityPhase ratio slope) (digit nextDigit : Bool × Bool)
    (exclusive : AffineExclusiveRegion ratio slope level digit)
    (next_exclusive : AffineExclusiveRegion ratio slope nextLevel nextDigit)
    (recurrence : level = affineChildOffset ratio slope digit + ratio*nextLevel) :
    (digit = (true,false) → nextDigit = (true,false)) ∧
    (digit = (false,true) → nextDigit = (false,true)) ∧
    (digit = (false,false) → nextDigit ≠ (true,true)) ∧
    (digit = (true,true) → nextDigit ≠ (false,false)) := by
  have slope_positive : 0 < slope := by linarith [phase.1]
  have lower_comparison := phase.2.1
  have upper_comparison := phase.2.2
  rcases digit with ⟨first, second⟩
  rcases nextDigit with ⟨nextFirst, nextSecond⟩
  cases first <;> cases second <;> cases nextFirst <;> cases nextSecond <;>
    simp_all [AffineExclusiveRegion, affineChildOffset] <;>
    nlinarith [mul_pos positive slope_positive]

theorem mixed_phase_exclusive_address_periodic {ratio slope : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2)
    (phase : MixedPeriodicityPhase ratio slope) (orbit : ℕ → ℝ)
    (digits : ℕ → Bool × Bool)
    (exclusive : ∀ depth, AffineExclusiveRegion ratio slope (orbit depth) (digits depth))
    (recurrence : ∀ depth,
      orbit depth = affineChildOffset ratio slope (digits depth) + ratio*orbit (depth+1)) :
    EventuallyPeriodicPairedAddress digits := by
  classical
  have transition := fun depth => mixed_phase_exclusive_transition positive less_half phase
    (digits depth) (digits (depth+1)) (exclusive depth) (exclusive (depth+1)) (recurrence depth)
  by_cases mixed : ∃ prefixLength, digits prefixLength = (true,false) ∨ digits prefixLength = (false,true)
  · obtain ⟨prefixLength, first | second⟩ := mixed
    · have constant : ∀ index, digits (prefixLength+index) = (true,false) := by
        intro index
        induction index with
        | zero => simpa using first
        | succ index induction => exact (transition (prefixLength+index)).1 induction
      refine ⟨prefixLength, 1, by decide, ?_⟩
      intro index
      rw [show index+prefixLength+1 = prefixLength+(index+1) by omega,
        show index+prefixLength = prefixLength+index by omega, constant, constant]
    · have constant : ∀ index, digits (prefixLength+index) = (false,true) := by
        intro index
        induction index with
        | zero => simpa using second
        | succ index induction => exact (transition (prefixLength+index)).2.1 induction
      refine ⟨prefixLength, 1, by decide, ?_⟩
      intro index
      rw [show index+prefixLength+1 = prefixLength+(index+1) by omega,
        show index+prefixLength = prefixLength+index by omega, constant, constant]
  · push_neg at mixed
    refine ⟨0, 1, by decide, ?_⟩
    intro index
    change digits (index+1) = digits index
    have previous := mixed index
    have next := mixed (index+1)
    have step := transition index
    rcases firstDigit : digits index with ⟨first, second⟩
    rcases secondDigit : digits (index+1) with ⟨nextFirst, nextSecond⟩
    cases first <;> cases second <;> cases nextFirst <;> cases nextSecond <;>
      simp [firstDigit, secondDigit] at previous next step ⊢

theorem paired_periodic_coordinates_in_parameterField {ratio : ℝ}
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    {digits : ℕ → Bool × Bool} (periodic : EventuallyPeriodicPairedAddress digits) :
    address ratio (fun index => (digits index).1) ∈ parameterField ratio ∧
      address ratio (fun index => (digits index).2) ∈ parameterField ratio := by
  obtain ⟨prefixLength, period, period_positive, periodic⟩ := periodic
  constructor
  · exact eventually_periodic_address_mem_parameterField nonnegative less_one _ prefixLength period
      period_positive (fun index => congrArg Prod.fst (periodic index))
  · exact eventually_periodic_address_mem_parameterField nonnegative less_one _ prefixLength period
      period_positive (fun index => congrArg Prod.snd (periodic index))

end LambdaCantor.Last
