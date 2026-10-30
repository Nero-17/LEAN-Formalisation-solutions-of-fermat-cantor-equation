import LambdaCantor.Half
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FunProp

noncomputable section
namespace LambdaCantor

def curvePoint (exponent x : ℝ) : ℝ × ℝ :=
  (x, (1 - x ^ exponent) ^ exponent⁻¹)

theorem contDiffOn_curvePoint {exponent : ℝ} (positive : 0 < exponent) :
    ContDiffOn ℝ 1 (curvePoint exponent) (Set.Ioo 0 1) := by
  have first_power : ContDiffOn ℝ 1 (fun x : ℝ => x ^ exponent) (Set.Ioo 0 1) :=
    contDiffOn_id.rpow_const_of_ne (fun _ membership => ne_of_gt membership.1)
  have second_power : ContDiffOn ℝ 1
      (fun x : ℝ => (1 - x ^ exponent) ^ exponent⁻¹) (Set.Ioo 0 1) := by
    apply (contDiffOn_const.sub first_power).rpow_const_of_ne
    intro x membership
    exact ne_of_gt (sub_pos.mpr (Real.rpow_lt_one membership.1.le membership.2 positive))
  exact contDiffOn_id.prodMk second_power

theorem intersection_subset_curve {exponent ratio : ℝ} (positive : 0 < exponent)
    (ratio_nonnegative : 0 ≤ ratio) (ratio_lt_one : ratio < 1) :
    intersection exponent ratio ⊆
      {curvePoint exponent 0} ∪ {curvePoint exponent 1} ∪
        curvePoint exponent '' Set.Ioo 0 1 := by
  rintro ⟨x, y⟩ membership
  have x_bounds := cantorSet_subset_unitInterval ratio_nonnegative ratio_lt_one membership.1
  have y_bounds := cantorSet_subset_unitInterval ratio_nonnegative ratio_lt_one membership.2.1
  have curve_eq : curvePoint exponent x = (x, y) := by
    apply Prod.ext
    · rfl
    dsimp [curvePoint]
    have residual_eq : 1 - x ^ exponent = y ^ exponent := by linarith [membership.2.2]
    rw [residual_eq, Real.rpow_rpow_inv y_bounds.1 (ne_of_gt positive)]
  rw [← curve_eq]
  by_cases x_zero : x = 0
  · subst x
    exact Or.inl (Or.inl rfl)
  by_cases x_one : x = 1
  · subst x
    exact Or.inl (Or.inr rfl)
  exact Or.inr ⟨x, ⟨lt_of_le_of_ne x_bounds.1 (Ne.symm x_zero),
    lt_of_le_of_ne x_bounds.2 x_one⟩, rfl⟩

theorem dimH_intersection_le_one {exponent ratio : ℝ} (positive : 0 < exponent)
    (ratio_nonnegative : 0 ≤ ratio) (ratio_lt_one : ratio < 1) :
    dimH (intersection exponent ratio) ≤ 1 := by
  have image_bound := (contDiffOn_curvePoint positive).dimH_image_le
    (convex_Ioo (0 : ℝ) 1) (Set.Subset.refl _)
  have interval_bound : dimH (Set.Ioo (0 : ℝ) 1) ≤ 1 := by
    simpa only [Real.dimH_univ] using dimH_mono (Set.subset_univ (Set.Ioo (0 : ℝ) 1))
  have full_bound := dimH_mono (intersection_subset_curve positive ratio_nonnegative ratio_lt_one)
  simp only [dimH_union, dimH_singleton, max_self] at full_bound
  exact full_bound.trans (max_le (by norm_num) (image_bound.trans interval_bound))

theorem dimH_intersection_half {exponent : ℝ} (positive : 0 < exponent) :
    dimH (intersection exponent (1 / 2)) = 1 := by
  exact le_antisymm (dimH_intersection_le_one positive (by norm_num) (by norm_num))
    (one_le_dimH_intersection_half positive)

end LambdaCantor
