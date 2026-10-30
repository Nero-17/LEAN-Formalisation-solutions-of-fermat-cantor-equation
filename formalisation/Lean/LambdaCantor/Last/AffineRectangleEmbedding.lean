import LambdaCantor.Last.ScalarCylinders
import Mathlib.Topology.MetricSpace.HausdorffDimension

noncomputable section
namespace LambdaCantor.Last
open scoped NNReal

def affineRectangleEmbedding (firstLeft firstScale secondLeft secondScale : ℝ)
    (point : ℝ × ℝ) : ℝ × ℝ :=
  (firstLeft+firstScale*point.1, secondLeft+secondScale*point.2)

theorem affineRectangleEmbedding_antilipschitz {firstScale secondScale : ℝ}
    (first_positive : 0 < firstScale) (second_positive : 0 < secondScale)
    (firstLeft secondLeft : ℝ) :
    AntilipschitzWith
      (⟨max firstScale⁻¹ secondScale⁻¹, le_max_of_le_left (inv_nonneg.mpr first_positive.le)⟩ : ℝ≥0)
      (affineRectangleEmbedding firstLeft firstScale secondLeft secondScale) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro first second
  change dist first second ≤ max firstScale⁻¹ secondScale⁻¹ *
    dist (affineRectangleEmbedding firstLeft firstScale secondLeft secondScale first)
      (affineRectangleEmbedding firstLeft firstScale secondLeft secondScale second)
  have first_distance : dist
      (affineRectangleEmbedding firstLeft firstScale secondLeft secondScale first).1
      (affineRectangleEmbedding firstLeft firstScale secondLeft secondScale second).1 =
      firstScale*dist first.1 second.1 := by
    simp only [affineRectangleEmbedding, dist_add_left, Real.dist_eq]
    rw [← mul_sub, abs_mul, abs_of_pos first_positive]
  have second_distance : dist
      (affineRectangleEmbedding firstLeft firstScale secondLeft secondScale first).2
      (affineRectangleEmbedding firstLeft firstScale secondLeft secondScale second).2 =
      secondScale*dist first.2 second.2 := by
    simp only [affineRectangleEmbedding, dist_add_left, Real.dist_eq]
    rw [← mul_sub, abs_mul, abs_of_pos second_positive]
  rw [Prod.dist_eq, Prod.dist_eq, first_distance, second_distance]
  apply max_le
  · calc
      dist first.1 second.1 = firstScale⁻¹*(firstScale*dist first.1 second.1) := by
        rw [← mul_assoc, inv_mul_cancel₀ first_positive.ne', one_mul]
      _ ≤ max firstScale⁻¹ secondScale⁻¹ * (firstScale*dist first.1 second.1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg first_positive.le dist_nonneg)
      _ ≤ max firstScale⁻¹ secondScale⁻¹ *
          max (firstScale*dist first.1 second.1) (secondScale*dist first.2 second.2) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (le_max_of_le_left (inv_nonneg.mpr first_positive.le))
  · calc
      dist first.2 second.2 = secondScale⁻¹*(secondScale*dist first.2 second.2) := by
        rw [← mul_assoc, inv_mul_cancel₀ second_positive.ne', one_mul]
      _ ≤ max firstScale⁻¹ secondScale⁻¹ * (secondScale*dist first.2 second.2) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg second_positive.le dist_nonneg)
      _ ≤ max firstScale⁻¹ secondScale⁻¹ *
          max (firstScale*dist first.1 second.1) (secondScale*dist first.2 second.2) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (le_max_of_le_left (inv_nonneg.mpr first_positive.le))

theorem cantor_power_scale_mem {ratio coordinate : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (depth : ℕ) (membership : coordinate ∈ cantorSet ratio) :
    ratio^depth*coordinate ∈ cantorSet ratio := by
  induction depth with
  | zero => simpa using membership
  | succ depth induction =>
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
      low_copy_mem nonnegative less_one induction

end LambdaCantor.Last
