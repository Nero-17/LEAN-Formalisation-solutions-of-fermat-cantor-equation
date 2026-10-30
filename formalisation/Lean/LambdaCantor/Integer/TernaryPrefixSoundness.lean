import LambdaCantor.Certificates.IntegerSmallSources
import LambdaCantor.Classical.Source
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace LambdaCantor.Integer

/-- The finite padded ternary checker really certifies a Cantor-cylinder embedding. -/
theorem ternaryPrefix_cantor_embedding (word depth : ℕ)
    (accepted : ternaryPrefix word depth = true) (point : ℝ)
    (membership : point ∈ cantorSet (1/3)) :
    ((word : ℝ)+point)/3^depth ∈ cantorSet (1/3) := by
  induction depth generalizing word point with
  | zero =>
    simp only [ternaryPrefix, beq_iff_eq] at accepted
    simpa [accepted] using membership
  | succ depth inductionHypothesis =>
    simp only [ternaryPrefix, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at accepted
    have tail_member : ((word%3 : ℕ) + point)/3 ∈ cantorSet (1/3) := by
      rw [cantorSet_third_eq] at membership ⊢
      rcases accepted.1 with zero | two
      · simpa only [zero, Nat.cast_zero, zero_add] using Classical.cantor_prepend_zero membership
      · simpa only [two, Nat.cast_ofNat] using Classical.cantor_prepend_two membership
    have retained := inductionHypothesis (word/3) accepted.2 _ tail_member
    have decomposition : (word : ℝ) = 3*(word/3 : ℕ) + (word%3 : ℕ) := by
      exact_mod_cast (Nat.div_add_mod word 3).symm
    have identity : ((word : ℝ)+point)/3^(depth+1) =
        ((word/3 : ℕ) + ((word%3 : ℕ) + point)/3)/3^depth := by
      rw [decomposition, pow_succ]
      field_simp
      <;> ring
    rw [identity]
    exact retained

end LambdaCantor.Integer
