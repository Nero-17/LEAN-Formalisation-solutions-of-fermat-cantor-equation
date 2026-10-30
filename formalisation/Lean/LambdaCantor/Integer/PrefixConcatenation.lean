import LambdaCantor.Certificates.IntegerSmallSources
import Mathlib.Tactic.Ring

namespace LambdaCantor.Integer

theorem ternaryPrefix_zero (depth : ℕ) : ternaryPrefix 0 depth = true := by
  induction depth with
  | zero => rfl
  | succ depth ih => simpa [ternaryPrefix] using ih

theorem ternaryPrefix_append (first last firstDepth lastDepth : ℕ)
    (firstValid : ternaryPrefix first firstDepth = true)
    (lastValid : ternaryPrefix last lastDepth = true) :
    ternaryPrefix (first*3^lastDepth+last) (firstDepth+lastDepth) = true := by
  induction lastDepth generalizing last with
  | zero =>
    simp only [ternaryPrefix,beq_iff_eq] at lastValid
    subst last
    simpa using firstValid
  | succ lastDepth ih =>
    have identity : first*3^(lastDepth+1)+last = 3*(first*3^lastDepth)+last := by
      rw [pow_succ]
      ring
    rw [identity,← Nat.add_assoc]
    simp only [ternaryPrefix,Bool.and_eq_true] at lastValid ⊢
    constructor
    · simpa only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod,Nat.zero_add,Nat.mod_mod]
        using lastValid.1
    · simpa only [Nat.mul_add_div (by decide : 0 < 3)] using ih (last/3) lastValid.2

theorem ternaryPrefix_pad (word depth padding : ℕ) (valid : ternaryPrefix word depth = true) :
    ternaryPrefix word (depth+padding) = true := by
  simpa only [Nat.zero_mul,Nat.zero_add,Nat.add_zero,Nat.add_comm] using
    ternaryPrefix_append 0 word padding depth (ternaryPrefix_zero padding) valid

theorem ternaryPrefix_bound (word depth : ℕ) (valid : ternaryPrefix word depth = true) :
    word+1 ≤ 3^depth := by
  induction depth generalizing word with
  | zero =>
    simp only [ternaryPrefix,beq_iff_eq] at valid
    subst word
    decide
  | succ depth ih =>
    simp only [ternaryPrefix,Bool.and_eq_true] at valid
    have quotient := ih (word/3) valid.2
    have remainder := Nat.mod_lt word (by decide : 0 < 3)
    have decomposition := Nat.mod_add_div word 3
    rw [pow_succ]
    omega

end LambdaCantor.Integer
