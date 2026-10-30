import LambdaCantor.Last.AnalyticIsolatedActualFilling

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

theorem wordMap_coordinate_order {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (word : List (Bool × Bool)) {first second : ℝ × ℝ}
    (ordered : first.1 ≤ second.1 ∧ first.2 ≤ second.2) :
    (wordMap ratio word first).1 ≤ (wordMap ratio word second).1 ∧
      (wordMap ratio word first).2 ≤ (wordMap ratio word second).2 := by
  rw [wordMap_affine ratio word first, wordMap_affine ratio word second]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor
  · exact add_le_add_right (mul_le_mul_of_nonneg_left ordered.1 (pow_nonneg nonnegative _)) _
  · exact add_le_add_right (mul_le_mul_of_nonneg_left ordered.2 (pow_nonneg nonnegative _)) _

/-- Positive coordinate order of an affine model is preserved on its actual
dust cylinder by a residual Lipschitz constant at most one. -/
theorem actual_increasing_of_cylinder_error {ratio slope : ℝ} (slope_lower : 1 ≤ slope)
    (function : (ℝ × ℝ) → ℝ) (word : List (Bool × Bool)) {bound : ℝ≥0}
    (bound_small : (bound : ℝ) ≤ 1)
    (error_lipschitz : LipschitzOnWith bound
      (fun value => function value-positiveLinearContinuous slope value) (wordCylinder ratio word))
    {first second : ℝ × ℝ} (first_mem : first ∈ wordCylinder ratio word)
    (second_mem : second ∈ wordCylinder ratio word)
    (ordered : first.1 ≤ second.1 ∧ first.2 ≤ second.2) : function first ≤ function second := by
  have first_difference_nonnegative := sub_nonneg.mpr ordered.1
  have second_difference_nonnegative := sub_nonneg.mpr ordered.2
  have linear_lower : dist second first ≤
      positiveLinearContinuous slope second-positiveLinearContinuous slope first := by
    simp only [Prod.dist_eq, Real.dist_eq,
      abs_of_nonneg first_difference_nonnegative, abs_of_nonneg second_difference_nonnegative]
    apply max_le
    · change second.1-first.1 ≤ (second.1+slope*second.2)-(first.1+slope*first.2)
      nlinarith [mul_nonneg (show 0 ≤ slope by linarith) second_difference_nonnegative]
    · change second.2-first.2 ≤ (second.1+slope*second.2)-(first.1+slope*first.2)
      nlinarith [mul_nonneg (sub_nonneg.mpr slope_lower) second_difference_nonnegative]
  have error_bound := error_lipschitz.dist_le_mul second second_mem first first_mem
  rw [Real.dist_eq] at error_bound
  have residual_lower := (abs_le.mp error_bound).1
  have contraction : (bound : ℝ)*dist second first ≤ dist second first :=
    mul_le_of_le_one_left dist_nonneg bound_small
  nlinarith

end LambdaCantor.Last
