import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section
namespace LambdaCantor.Last

/-- Choose a geometric scale with strict room for the cylinder-separation test. -/
theorem exists_geometric_depth {ratio separation diameter : ℝ}
    (hratio : 0 < ratio) (hratio_one : ratio < 1)
    (hseparation : 0 < separation) (hdiameter : 0 < diameter)
    (hsmall : diameter ≤ separation / 2) :
    ∃ depth : ℕ,
      diameter < separation * ratio ^ depth ∧
      ratio ^ depth ≤ (2 / (separation * ratio)) * diameter := by
  have hx : 0 < diameter / (separation / 2) := div_pos hdiameter (by linarith)
  have hxone : diameter / (separation / 2) ≤ 1 :=
    (div_le_one (by linarith)).mpr hsmall
  obtain ⟨depth, hnext, hcurrent⟩ :=
    exists_nat_pow_near_of_lt_one hx hxone hratio hratio_one
  refine ⟨depth, ?_, ?_⟩
  · have hle : diameter ≤ ratio ^ depth * (separation / 2) :=
      (div_le_iff₀ (by linarith)).mp hcurrent
    have hpow := pow_pos hratio depth
    nlinarith
  · have hlt : ratio ^ (depth + 1) * (separation / 2) < diameter :=
      (lt_div_iff₀ (by linarith)).mp hnext
    rw [pow_succ] at hlt
    have hproduct : 0 < separation * ratio := mul_pos hseparation hratio
    have hquotient : ratio ^ depth ≤ (2 * diameter) / (separation * ratio) :=
      (le_div_iff₀ hproduct).mpr (by nlinarith)
    convert hquotient using 1 <;> ring

/-- The strictly positive exponent matched to binary branching. -/
theorem binary_exponent_positive {ratio : ℝ} (hratio : 0 < ratio) (hratio_one : ratio < 1) :
    0 < Real.log (1 / 2) / Real.log ratio := by
  exact div_pos_of_neg_of_neg (Real.log_neg (by norm_num) (by norm_num))
    (Real.log_neg hratio hratio_one)

/-- The matching exponent sends a geometric cylinder contraction to half mass. -/
theorem binary_exponent_rpow {ratio : ℝ} (hratio : 0 < ratio) (hratio_one : ratio < 1) :
    ratio ^ (Real.log (1 / 2) / Real.log ratio) = (1 / 2 : ℝ) := by
  rw [Real.rpow_def_of_pos hratio]
  have hlog : Real.log ratio ≠ 0 := ne_of_lt (Real.log_neg hratio hratio_one)
  have hcancel : Real.log ratio * (Real.log (1 / 2) / Real.log ratio) =
      Real.log (1 / 2) := by field_simp
  rw [hcancel, Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]

end LambdaCantor.Last
