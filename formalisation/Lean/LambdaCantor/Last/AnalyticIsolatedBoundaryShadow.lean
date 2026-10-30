import LambdaCantor.Last.AnalyticIsolatedShadowing
import LambdaCantor.Last.AnalyticIsolatedBoundaryDigits

noncomputable section
namespace LambdaCantor.Last

def boundaryCentre (ratio : ℝ) (bit : Bool) : ℝ :=
  if bit then 1+2*ratio else 1-ratio

def boundaryChildOffset (ratio : ℝ) (digit : Bool × Bool) : ℝ :=
  (1-ratio)*((if digit.1 then 1 else 0)+(1+ratio)*(if digit.2 then 1 else 0))

/-- The limiting exclusive sets at the critical phase, with the endpoint
Taylor error displayed. This hypothesis is stronger than a bare tangent
equation and must be established from actual unique-child isolation. -/
def BoundaryApproxExclusive (ratio level error : ℝ) (digit : Bool × Bool) : Prop :=
  match digit with
  | (false,false) => level ≤ 1-ratio+error
  | (true,false) => |level-(1/2+ratio)| ≤ error
  | (false,true) => |level-3/2| ≤ error
  | (true,true) => 1+2*ratio-error ≤ level

theorem boundaryCentre_recurrence {ratio : ℝ}
    (critical_equation : 2*ratio^2+2*ratio=1) (bit : Bool) :
    boundaryCentre ratio bit = boundaryChildOffset ratio (bit,bit)+
      ratio*boundaryCentre ratio (!bit) := by
  cases bit <;> simp [boundaryCentre, boundaryChildOffset] <;> nlinarith

theorem boundary_wrong_digit_separation {ratio level error : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2)
    (bit : Bool) (digit : Bool × Bool)
    (exclusive : BoundaryApproxExclusive ratio level error digit)
    (wrong : digit ≠ (bit,bit)) :
    2*ratio-1/2 ≤ |level-boundaryCentre ratio bit|+error := by
  rcases digit with ⟨first, second⟩
  cases bit <;> cases first <;> cases second <;>
    simp_all only [BoundaryApproxExclusive, boundaryCentre, Bool.false_eq_true,
      if_false, if_true, Prod.mk.injEq, and_self, not_true_eq_false, ne_eq,
      not_false_eq_true, abs_le] <;>
    first
      | contradiction
      | nlinarith [le_abs_self (level-(1-ratio)), neg_le_abs (level-(1-ratio)),
          le_abs_self (level-(1+2*ratio)), neg_le_abs (level-(1+2*ratio))]

theorem boundary_mixed_centres {ratio : ℝ}
    (critical_equation : 2*ratio^2+2*ratio=1) :
    1/2+ratio = boundaryChildOffset ratio (true,false)+ratio*boundaryCentre ratio false ∧
      (3/2 : ℝ) = boundaryChildOffset ratio (false,true)+ratio*boundaryCentre ratio true := by
  constructor <;> simp [boundaryChildOffset, boundaryCentre] <;> nlinarith

/-- Exact boundary recurrence plus the actual exponentially small exclusive
set errors forces the long alternating blocks required by Theorem 5. The
loss is a single fixed integer, independent of the mixed-digit depth. -/
theorem boundary_shadowing_long_blocks {ratio coefficient : ℝ}
    (critical : ratio = (Real.sqrt 3-1)/2) (coefficient_positive : 0 < coefficient)
    (orbit : ℕ → ℝ) (digits : ℕ → Bool × Bool) (errors : ℕ → ℝ)
    (recurrence : ∀ depth, orbit depth = boundaryChildOffset ratio (digits depth)+
      ratio*orbit (depth+1))
    (exclusive : ∀ depth, BoundaryApproxExclusive ratio (orbit depth) (errors depth) (digits depth))
    (error_bound : ∀ depth, errors depth ≤ coefficient*ratio^depth)
    (mixed_unbounded : ∀ threshold : ℕ, ∃ depth : ℕ, threshold ≤ depth ∧
      (digits depth = (true,false) ∨ digits depth = (false,true))) :
    ∃ fixedLoss : ℕ, ∀ threshold : ℕ, ∃ start : ℕ, threshold ≤ start ∧
      IntegerAlternatingBlock (fun index => if (digits index).1 then 1 else 0)
        start (start-fixedLoss) ∧
      IntegerAlternatingBlock (fun index => if (digits index).2 then 1 else 0)
        start (start-fixedLoss) := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have ratio_positive : 0 < ratio := by rw [critical]; nlinarith
  have ratio_less_half : ratio < 1/2 := by rw [critical]; nlinarith
  have ratio_less_one : ratio < 1 := by linarith
  have critical_equation : 2*ratio^2+2*ratio=1 := by rw [critical]; nlinarith
  have separation_positive : 0 < 2*ratio-1/2 := by rw [critical]; nlinarith
  obtain ⟨loss, small⟩ := exists_pow_lt_of_lt_one
    (div_pos separation_positive (mul_pos (by norm_num : (0 : ℝ) < 2) coefficient_positive))
    ratio_less_one
  have room : 2*(coefficient*ratio^loss) < 2*ratio-1/2 := by
    have bound := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) coefficient_positive)).mp small
    nlinarith
  refine ⟨loss+2, ?_⟩
  intro threshold
  obtain ⟨depth, depth_lower, first_mixed | second_mixed⟩ :=
    mixed_unbounded (max threshold (loss+2))
  all_goals
    have threshold_lower : threshold ≤ depth+1 := by omega
    have depth_large : loss+2 ≤ depth := (le_max_right _ _).trans depth_lower
    have choose_initial : ∃ initial : Bool,
        |orbit depth-(boundaryChildOffset ratio (digits depth)+ratio*boundaryCentre ratio initial)| ≤
          errors depth := by
      first
        | refine ⟨false, ?_⟩
          have bound := exclusive depth
          rw [first_mixed] at bound ⊢
          rw [← (boundary_mixed_centres critical_equation).1]
          exact bound
        | refine ⟨true, ?_⟩
          have bound := exclusive depth
          rw [second_mixed] at bound ⊢
          rw [← (boundary_mixed_centres critical_equation).2]
          exact bound
    obtain ⟨initial, initial_bound⟩ := choose_initial
    have residual_identity : orbit depth-
        (boundaryChildOffset ratio (digits depth)+ratio*boundaryCentre ratio initial) =
        ratio*(orbit (depth+1)-boundaryCentre ratio initial) := by
      rw [recurrence depth]
      ring
    have initial_next : |orbit (depth+1)-boundaryCentre ratio initial| ≤
        coefficient*ratio^(depth-1) := by
      have power_step : ratio^(depth-1)*ratio = ratio^depth := by
        rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ depth by omega)]
      apply (mul_le_mul_iff_left₀ ratio_positive).mp
      calc
        |orbit (depth+1)-boundaryCentre ratio initial| * ratio =
            |orbit depth-(boundaryChildOffset ratio (digits depth)+ratio*boundaryCentre ratio initial)| := by
          rw [residual_identity, abs_mul, abs_of_pos ratio_positive]
          ring
        _ ≤ coefficient*ratio^depth := initial_bound.trans (error_bound depth)
        _ = coefficient*ratio^(depth-1)*ratio := by
          rw [← power_step]
          ring
    have initial_scaled : |orbit (depth+1)-boundaryCentre ratio initial| ≤
        (coefficient*ratio^loss)*ratio^((depth+1)-(loss+2)) := by
      convert initial_next using 1
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    have small_errors : ∀ position < (depth+1)-(loss+2),
        errors ((depth+1)+position) ≤ coefficient*ratio^loss := by
      intro position _
      exact (error_bound _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one ratio_positive.le ratio_less_one.le (by omega)) coefficient_positive.le)
    have shadow := two_cycle_shadowing ratio_positive ratio_less_one
      (mul_nonneg coefficient_positive.le (pow_nonneg ratio_positive.le loss)) room
      orbit digits errors (boundaryChildOffset ratio) (boundaryCentre ratio) recurrence
      (boundaryCentre_recurrence critical_equation)
      (fun depth bit wrong => boundary_wrong_digit_separation ratio_positive ratio_less_half
        bit (digits depth) (exclusive depth) wrong)
      (depth+1) ((depth+1)-(loss+2)) initial initial_scaled small_errors
    exact ⟨depth+1, threshold_lower,
      (boolean_integer_alternating_of_paired_shadow digits initial _ _ shadow).1,
      (boolean_integer_alternating_of_paired_shadow digits initial _ _ shadow).2⟩

end LambdaCantor.Last
