import LambdaCantor.Last.ArithmeticStammering
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor.Last

def alternatingBit (initial : Bool) : ℕ → Bool
  | 0 => initial
  | depth+1 => !(alternatingBit initial depth)

/-- A finite horizon of the exact two-cycle shadowing argument. The input
`wrong_digit_separation` is the geometric distance from each cycle centre to
every wrong exclusive region, with the endpoint linearization error added.
This lemma propagates the initial error and forces all intervening symbols. -/
theorem two_cycle_shadowing
    {ratio tolerance separation : ℝ} (positive : 0 < ratio) (less_one : ratio < 1)
    (tolerance_nonnegative : 0 ≤ tolerance) (room : 2*tolerance < separation)
    (orbit : ℕ → ℝ) (digits : ℕ → Bool × Bool) (errors : ℕ → ℝ)
    (offset : Bool × Bool → ℝ) (centres : Bool → ℝ)
    (orbit_recurrence : ∀ depth, orbit depth = offset (digits depth)+ratio*orbit (depth+1))
    (centre_recurrence : ∀ bit, centres bit = offset (bit,bit)+ratio*centres (!bit))
    (wrong_digit_separation : ∀ depth bit, digits depth ≠ (bit,bit) →
      separation ≤ |orbit depth-centres bit|+errors depth)
    (start horizon : ℕ) (initial : Bool)
    (initial_error : |orbit start-centres initial| ≤ tolerance*ratio^horizon)
    (errors_small : ∀ depth < horizon, errors (start+depth) ≤ tolerance) :
    ∀ depth < horizon, digits (start+depth) =
      (alternatingBit initial depth, alternatingBit initial depth) := by
  have invariant : ∀ depth, depth ≤ horizon →
      |orbit (start+depth)-centres (alternatingBit initial depth)| ≤
        tolerance*ratio^(horizon-depth) ∧
      (depth < horizon → digits (start+depth) =
        (alternatingBit initial depth, alternatingBit initial depth)) := by
    intro depth
    induction depth with
    | zero =>
      intro _
      have close : |orbit (start+0)-centres (alternatingBit initial 0)| ≤
          tolerance*ratio^(horizon-0) := by simpa [alternatingBit] using initial_error
      refine ⟨close, ?_⟩
      intro active
      by_contra different
      have separated := wrong_digit_separation (start+0) initial (by
        simpa [alternatingBit] using different)
      have close_uniform : |orbit (start+0)-centres initial| ≤ tolerance := by
        exact (show |orbit (start+0)-centres initial| ≤ tolerance*ratio^horizon by
          simpa [alternatingBit] using close).trans
          (mul_le_of_le_one_right tolerance_nonnegative (pow_le_one₀ positive.le less_one.le))
      have small := errors_small 0 active
      linarith
    | succ depth induction =>
      intro depth_bound
      have previous := induction (by omega)
      have previous_digit := previous.2 (by omega)
      have orbit_step := orbit_recurrence (start+depth)
      rw [previous_digit] at orbit_step
      have centre_step := centre_recurrence (alternatingBit initial depth)
      have residual_identity : orbit (start+depth)-centres (alternatingBit initial depth) =
          ratio*(orbit (start+(depth+1))-centres (alternatingBit initial (depth+1))) := by
        simp only [alternatingBit]
        have natural_eq : start+depth+1 = start+(depth+1) := by omega
        rw [natural_eq] at orbit_step
        rw [orbit_step, centre_step]
        ring
      have residual_norm := congrArg abs residual_identity
      rw [abs_mul, abs_of_pos positive] at residual_norm
      have exponent_identity : horizon-depth = (horizon-(depth+1))+1 := by omega
      have close : |orbit (start+(depth+1))-centres (alternatingBit initial (depth+1))| ≤
          tolerance*ratio^(horizon-(depth+1)) := by
        apply (mul_le_mul_iff_right₀ positive).mp
        calc
          ratio*|orbit (start+(depth+1))-centres (alternatingBit initial (depth+1))| =
              |orbit (start+depth)-centres (alternatingBit initial depth)| := residual_norm.symm
          _ ≤ tolerance*ratio^(horizon-depth) := previous.1
          _ = ratio*(tolerance*ratio^(horizon-(depth+1))) := by
            rw [exponent_identity, pow_succ]
            ring
      refine ⟨close, ?_⟩
      intro active
      by_contra different
      have separated := wrong_digit_separation (start+(depth+1))
        (alternatingBit initial (depth+1)) different
      have close_uniform : |orbit (start+(depth+1))-centres (alternatingBit initial (depth+1))| ≤
          tolerance := close.trans
        (mul_le_of_le_one_right tolerance_nonnegative (pow_le_one₀ positive.le less_one.le))
      have small := errors_small (depth+1) active
      linarith
  intro depth active
  exact (invariant depth active.le).2 active

theorem boolean_integer_alternating_of_paired_shadow
    (digits : ℕ → Bool × Bool) (initial : Bool) (start length : ℕ)
    (shadow : ∀ depth < length, digits (start+depth) =
      (alternatingBit initial depth, alternatingBit initial depth)) :
    IntegerAlternatingBlock (fun index => if (digits index).1 then 1 else 0) start length ∧
      IntegerAlternatingBlock (fun index => if (digits index).2 then 1 else 0) start length := by
  constructor <;> intro depth active <;>
    dsimp only <;>
    rw [show start+depth+1 = start+(depth+1) by omega,
      shadow (depth+1) active, shadow depth (by omega)] <;>
    simp only [alternatingBit]
  all_goals
    by_cases bit_true : alternatingBit initial depth = true
    · simp [bit_true]
    · have bit_false : alternatingBit initial depth = false := Bool.eq_false_of_not_eq_true bit_true
      simp [bit_false]

end LambdaCantor.Last
