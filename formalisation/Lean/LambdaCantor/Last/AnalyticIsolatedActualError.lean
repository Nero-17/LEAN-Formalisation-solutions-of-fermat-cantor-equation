import LambdaCantor.Last.AnalyticIsolatedActualFilling

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

theorem normalized_actual_error_of_cylinder_lipschitz {ratio slope : ℝ}
    (positive : 0 < ratio) (less_one : ratio < 1)
    (function : (ℝ × ℝ) → ℝ) (word : List (Bool × Bool)) {bound : ℝ≥0}
    (lipschitz : LipschitzOnWith bound
      (fun value => function value-positiveLinearContinuous slope value) (wordCylinder ratio word))
    {tail : ℝ × ℝ} (tail_mem : tail ∈ cantorDust ratio) :
    |normalizedActualFunction function ratio word tail-positiveLinearContinuous slope tail| ≤ bound := by
  have scale_positive : 0 < ratio^word.length := pow_pos positive _
  have image_mem : wordMap ratio word tail ∈ wordCylinder ratio word := ⟨tail, tail_mem, rfl⟩
  have corner_mem : wordMap ratio word 0 ∈ wordCylinder ratio word :=
    ⟨0, ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩, rfl⟩
  have distance_bound := wordCylinder_dist_le positive.le less_one word image_mem corner_mem
  have error_bound := lipschitz.dist_le_mul (wordMap ratio word tail) image_mem
    (wordMap ratio word 0) corner_mem
  rw [Real.dist_eq] at error_bound
  have absolute_bound := error_bound.trans
    (mul_le_mul_of_nonneg_left distance_bound bound.coe_nonneg)
  have normalized_identity : normalizedActualFunction function ratio word tail-
      positiveLinearContinuous slope tail =
      ((function (wordMap ratio word tail)-positiveLinearContinuous slope (wordMap ratio word tail))-
        (function (wordMap ratio word 0)-positiveLinearContinuous slope (wordMap ratio word 0)))/
        ratio^word.length := by
    unfold normalizedActualFunction
    rw [wordMap_affine ratio word tail, map_add, map_smul]
    simp only [smul_eq_mul]
    field_simp [scale_positive.ne']
    ring
  rw [normalized_identity, abs_div, abs_of_pos scale_positive]
  exact (div_le_iff₀ scale_positive).mpr absolute_bound

end LambdaCantor.Last
