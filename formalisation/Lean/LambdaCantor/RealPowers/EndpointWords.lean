import LambdaCantor.RealPowers.SourceSelection
import LambdaCantor.Last.ScalarCylinders
import Mathlib.Data.List.OfFn

noncomputable section
namespace LambdaCantor.RealPowers
open Last

def scalarPrefix (digits : ℕ → Bool) (depth : ℕ) : List Bool :=
  List.ofFn (fun index : Fin depth => digits index)

@[simp] theorem scalarPrefix_length (digits : ℕ → Bool) (depth : ℕ) :
    (scalarPrefix digits depth).length = depth := by simp [scalarPrefix]

theorem prefixValue_first_digit (ratio : ℝ) (digits : ℕ → Bool) (depth : ℕ) :
    prefixValue ratio digits (depth+1) =
      (1-ratio)*(if digits 0 then (1 : ℝ) else 0)+
        ratio*prefixValue ratio (fun index => digits (index+1)) depth := by
  unfold prefixValue
  rw [Finset.sum_range_succ']
  simp_rw [pow_succ]
  simp only [pow_zero, mul_one]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  ring

theorem scalarPrefix_zero (ratio : ℝ) (digits : ℕ → Bool) (depth : ℕ) :
    scalarWordMap ratio (scalarPrefix digits depth) 0 = prefixValue ratio digits depth := by
  induction depth generalizing digits with
  | zero => simp [scalarPrefix, scalarWordMap, prefixValue]
  | succ depth inductionHypothesis =>
      simp only [scalarPrefix, List.ofFn_succ, scalarWordMap, Fin.val_succ, Fin.val_zero]
      rw [show (List.ofFn (fun index : Fin depth => digits (index.val+1))) =
          scalarPrefix (fun index => digits (index+1)) depth by rfl,
        inductionHypothesis, prefixValue_first_digit]
      cases first_digit : digits 0 <;> simp only [first_digit, Bool.false_eq_true, if_false, if_true] <;> ring

theorem finiteOuterEndpoint_word (digits : ℕ → Bool) (depth : ℕ) :
    scalarWordMap (1/3) (true::scalarPrefix digits depth) 0 = finiteOuterEndpoint digits depth := by
  simp only [scalarWordMap, if_true, scalarPrefix_zero, finiteOuterEndpoint]
  ring

@[simp] theorem zero_word_map (ratio : ℝ) (depth : ℕ) :
    scalarWordMap ratio (List.replicate depth false) 0 = 0 := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis => simp [List.replicate_succ, scalarWordMap, inductionHypothesis]

/-- Appending zero digits gives arbitrarily deep genuine cylinders with the
same positive finite left endpoint. -/
theorem append_zeros_left_endpoint (ratio : ℝ) (word : List Bool) (depth : ℕ) :
    scalarWordMap ratio (word++List.replicate depth false) 0 = scalarWordMap ratio word 0 := by
  rw [scalarWordMap_append, zero_word_map]

end LambdaCantor.RealPowers

