import LambdaCantor.AE.CenteredPrefixAverage
import LambdaCantor.AE.FreezingPowerComparison

noncomputable section
open Set

namespace LambdaCantor.AE

theorem centered_freezing_root_distance
    (root : (ℕ → Bool × Bool) → ℝ) (depth : ℕ)
    {displacementConstant rho upper : ℝ}
    (prefix_displacement : ∀ first second : ℕ → Bool × Bool,
      (∀ index < depth, first index = second index) →
      |root first-root second| ≤ displacementConstant*rho*upper^depth)
    (freezing : (Fin depth → Bool × Bool) → ℝ)
    (freezing_mem : ∀ word, freezing word ∈ centeredFreezingInterval root depth displacementConstant rho upper word)
    (digits : ℕ → Bool × Bool) :
    |root digits-freezing (fun index => digits index)| ≤ 2*displacementConstant*rho*upper^depth := by
  have prefix_bound := prefix_displacement digits
    (centeredPrefixRepresentative depth (fun index => digits index)) (by
      intro index before
      simp only [centeredPrefixRepresentative, dif_pos before])
  have freezing_bound := freezing_mem (fun index => digits index)
  change freezing (fun index => digits index) ∈ Icc _ _ at freezing_bound
  have root_bound := abs_le.mp prefix_bound
  apply abs_le.mpr
  constructor <;> nlinarith [root_bound.1, root_bound.2, freezing_bound.1, freezing_bound.2]

theorem centered_freezing_center_distance
    (root : (ℕ → Bool × Bool) → ℝ) (depth : ℕ)
    {center displacementConstant rho upper windowConstant : ℝ}
    (displacement_nonnegative : 0 ≤ displacementConstant) (rho_nonnegative : 0 ≤ rho)
    (upper_nonnegative : 0 ≤ upper) (upper_le_one : upper ≤ 1)
    (roots_window : ∀ digits, |root digits-center| ≤ windowConstant*rho)
    (freezing : (Fin depth → Bool × Bool) → ℝ)
    (freezing_mem : ∀ word, freezing word ∈ centeredFreezingInterval root depth displacementConstant rho upper word) :
    ∀ word, |freezing word-center| ≤ (windowConstant+displacementConstant)*rho := by
  intro word
  have membership := freezing_mem word
  change freezing word ∈ Icc _ _ at membership
  have root_bound := abs_le.mp (roots_window (centeredPrefixRepresentative depth word))
  have radius_bound := mul_le_mul_of_nonneg_left
    (pow_le_one₀ upper_nonnegative upper_le_one (n := depth))
    (mul_nonneg displacement_nonnegative rho_nonnegative)
  apply abs_le.mpr
  constructor <;> nlinarith [membership.1, membership.2, root_bound.1, root_bound.2]

theorem centered_adjacent_freezing_distance
    (root : (ℕ → Bool × Bool) → ℝ)
    {displacementConstant rho upper : ℝ}
    (displacement_nonnegative : 0 ≤ displacementConstant) (rho_nonnegative : 0 ≤ rho)
    (upper_nonnegative : 0 ≤ upper) (upper_le_one : upper ≤ 1)
    (prefix_displacement : ∀ (depth : ℕ) (first second : ℕ → Bool × Bool),
      (∀ index < depth, first index = second index) →
      |root first-root second| ≤ displacementConstant*rho*upper^depth)
    (freezing : ∀ depth, (Fin depth → Bool × Bool) → ℝ)
    (freezing_mem : ∀ depth word,
      freezing depth word ∈ centeredFreezingInterval root depth displacementConstant rho upper word)
    (depth : ℕ) (digits : ℕ → Bool × Bool) :
    |freezing depth (fun index => digits index)-freezing (depth+1) (fun index => digits index)| ≤
      4*displacementConstant*rho*upper^depth := by
  have first := centered_freezing_root_distance root depth (prefix_displacement depth)
    (freezing depth) (freezing_mem depth) digits
  have second := centered_freezing_root_distance root (depth+1) (prefix_displacement (depth+1))
    (freezing (depth+1)) (freezing_mem (depth+1)) digits
  have power_bound : upper^(depth+1) ≤ upper^depth := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg upper_nonnegative depth) upper_le_one
  have radius_bound := mul_le_mul_of_nonneg_left power_bound
    (show 0 ≤ 2*displacementConstant*rho by positivity)
  have triangle := abs_sub_le (freezing depth (fun index => digits index))
    (root digits) (freezing (depth+1) (fun index => digits index))
  rw [abs_sub_comm (freezing depth (fun index => digits index)) (root digits)] at triangle
  linarith

end LambdaCantor.AE
