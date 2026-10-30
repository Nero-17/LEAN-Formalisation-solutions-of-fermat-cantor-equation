import LambdaCantor.AE.CenteredPrefixTailSlope
import LambdaCantor.SelfSimilarity
import Lean.Elab.Tactic.Omega

noncomputable section
open Set
namespace LambdaCantor.AE

/-- Distinct finite first-coordinate prefixes are uniformly separated throughout
the fixed parameter band. -/
theorem centered_address_prefix_gap {lower upper ratio : ℝ}
    (lower_positive : 0 < lower) (upper_half : upper < 1/2)
    (ratio_mem : ratio ∈ Icc lower upper) (first other : ℕ → Bool) (depth : ℕ)
    (different : ∃ position < depth, first position ≠ other position) :
    (1-2*upper)*lower^depth ≤ |address ratio first-address ratio other| := by
  classical
  obtain ⟨position, before, differs⟩ := different
  have exists_difference : ∃ index, first index ≠ other index := ⟨position, differs⟩
  have first_before : Nat.find exists_difference ≤ position := Nat.find_min' exists_difference differs
  have gap := prefix_separation (lower_positive.trans_le ratio_mem.1)
    (ratio_mem.2.trans_lt upper_half) first other (Nat.find exists_difference)
    (fun index earlier => not_ne_iff.mp (Nat.find_min exists_difference earlier))
    (Nat.find_spec exists_difference)
  have lower_one : lower ≤ 1 := by linarith [ratio_mem.1, ratio_mem.2]
  have powers : lower^depth ≤ ratio^(Nat.find exists_difference) :=
    (pow_le_pow_of_le_one lower_positive.le lower_one (by omega)).trans
      (pow_le_pow_left₀ lower_positive.le ratio_mem.1 _)
  have product := mul_le_mul
    (show 1-2*upper ≤ 1-2*ratio by linarith [ratio_mem.2]) powers
    (pow_nonneg lower_positive.le depth) (by linarith [ratio_mem.2])
  exact product.trans gap

/-- Actual centred-residual geometry converts a uniform parameter derivative
upper bound to first-coordinate root separation on scale rho. -/
theorem centered_root_first_coordinate_separation
    {exponent lower upper rho derivativeBound : ℝ}
    (exponent_ge_one : 1 ≤ exponent) (lower_positive : 0 < lower) (upper_half : upper < 1/2)
    (rho_positive : 0 < rho) (derivative_positive : 0 < derivativeBound)
    (horizontalDepth verticalDepth tailDepth : ℕ)
    (root : (ℕ → Bool × Bool) → ℝ)
    (root_mem : ∀ digits, root digits ∈ Icc lower upper)
    (root_zero : ∀ digits, centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits (root digits) = 0)
    (root_power_lower : ∀ digits, rho/2 ≤ (root digits)^tailDepth)
    (root_power_small : ∀ digits, (root digits)^tailDepth ≤ 1/2)
    (differentiable : ∀ digits ratio, ratio ∈ Icc lower upper →
      DifferentiableAt ℝ (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) ratio)
    (derivative_bound : ∀ digits ratio, ratio ∈ Icc lower upper →
      |deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) ratio| ≤ derivativeBound)
    (second : ℕ → Bool) (depth : ℕ) (first other : ℕ → Bool)
    (different : ∃ position < depth, first position ≠ other position) :
    ((exponent*(1/2:ℝ)^(exponent-1))*(rho/2)*(1-2*upper)/derivativeBound)*lower^depth ≤
      |root (fun index => (first index, second index))-root (fun index => (other index, second index))| := by
  have root_positive := lower_positive.trans_le (root_mem (fun index => (first index, second index))).1
  have root_less_one : root (fun index => (first index, second index)) < 1 := by
    linarith [(root_mem (fun index => (first index, second index))).2]
  have tail_bound := centered_residual_first_tail_lower exponent_ge_one root_positive root_less_one
    horizontalDepth verticalDepth tailDepth (root_power_small (fun index => (first index, second index))) first other second
  have gap := centered_address_prefix_gap lower_positive upper_half (root_mem (fun index => (first index, second index))) first other depth different
  have coefficient_nonnegative : 0 ≤ exponent*(1/2:ℝ)^(exponent-1) := by positivity
  have scaled_gap := mul_le_mul
    (mul_le_mul_of_nonneg_left (root_power_lower (fun index => (first index, second index))) coefficient_nonnegative) gap
    (mul_nonneg (show 0 ≤ 1-2*upper by linarith [upper_half])
      (pow_nonneg lower_positive.le depth))
    (by positivity : 0 ≤ exponent*(1/2:ℝ)^(exponent-1)*(root (fun index => (first index, second index)))^tailDepth)
  have parameter_bound := (convex_Icc lower upper).norm_image_sub_le_of_norm_deriv_le
    (differentiable (fun index => (other index, second index)))
    (by simpa only [Real.norm_eq_abs] using derivative_bound (fun index => (other index, second index)))
    (root_mem (fun index => (other index, second index)))
    (root_mem (fun index => (first index, second index)))
  simp only [Real.norm_eq_abs] at parameter_bound
  rw [root_zero, sub_zero] at parameter_bound
  rw [root_zero, zero_sub, abs_neg] at tail_bound
  have combined := scaled_gap.trans (tail_bound.trans parameter_bound)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ derivative_positive).mpr
  nlinarith [combined]

end LambdaCantor.AE


