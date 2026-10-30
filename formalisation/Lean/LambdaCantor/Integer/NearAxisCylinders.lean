import LambdaCantor.Certificates.IntegerSmallSources
import LambdaCantor.ClassicalBridge
import LambdaCantor.Addresses
import Mathlib.Tactic.FieldSimp

namespace LambdaCantor.Integer

theorem ternaryPrefix_cylinder_mem (P p : ℕ) (valid : ternaryPrefix P p = true)
    (tail : ℝ) (member : tail ∈ _root_.cantorSet) :
    ((P : ℝ)+tail)/3^p ∈ _root_.cantorSet := by
  induction p generalizing P tail with
  | zero =>
    simp only [ternaryPrefix,beq_iff_eq] at valid
    subst P
    simpa using member
  | succ p ih =>
    simp only [ternaryPrefix,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at valid
    have childMember : ((P%3 : ℕ) : ℝ)/3+tail/3 ∈ _root_.cantorSet := by
      rw [_root_.cantorSet_eq_union_halves]
      rcases valid.1 with digit | digit
      · left
        refine ⟨tail,member,?_⟩
        simp [digit]
      · right
        refine ⟨tail,member,?_⟩
        simp only [digit,Nat.cast_ofNat]
        ring
    have result := ih (P/3) valid.2 _ childMember
    have decomposition : ((P%3 : ℕ) : ℝ)+3*((P/3 : ℕ) : ℝ) = (P : ℝ) := by
      exact_mod_cast Nat.mod_add_div P 3
    have identity : (((P/3 : ℕ) : ℝ)+(((P%3 : ℕ) : ℝ)/3+tail/3))/3^p =
        ((P : ℝ)+tail)/3^(p+1) := by
      rw [pow_succ]
      field_simp
      nlinarith
    rwa [identity] at result

theorem third_power_mem_cantor (depth : ℕ) (value : ℝ) (member : value ∈ _root_.cantorSet) :
    (1/3 : ℝ)^depth*value ∈ _root_.cantorSet := by
  induction depth with
  | zero => simpa using member
  | succ depth ih =>
    rw [_root_.cantorSet_eq_union_halves]
    left
    refine ⟨(1/3 : ℝ)^depth*value,ih,?_⟩
    rw [pow_succ]
    ring

theorem third_complement_mem_cantor (value : ℝ) (member : value ∈ _root_.cantorSet) :
    1-value ∈ _root_.cantorSet := by
  rw [← cantorSet_third_eq] at member ⊢
  exact one_sub_mem_cantorSet (by norm_num) (by norm_num) member

theorem near_axis_physical_cylinders (n d k P Q p q : ℕ)
    (prefixP : ternaryPrefix P p = true) (prefixQ : ternaryPrefix Q q = true)
    (first second : ℝ) (firstMember : first ∈ _root_.cantorSet)
    (secondMember : second ∈ _root_.cantorSet) :
    (1/3 : ℝ)^k*((P+first)/3^p) ∈ _root_.cantorSet ∧
    1-(1/3 : ℝ)^(n*k+d)*((Q+1-second)/3^q) ∈ _root_.cantorSet := by
  constructor
  · exact third_power_mem_cantor k _ (ternaryPrefix_cylinder_mem P p prefixP first firstMember)
  · apply third_complement_mem_cantor
    apply third_power_mem_cantor
    have reflected := ternaryPrefix_cylinder_mem Q q prefixQ (1-second)
      (third_complement_mem_cantor second secondMember)
    simpa only [add_sub_assoc] using reflected

end LambdaCantor.Integer
