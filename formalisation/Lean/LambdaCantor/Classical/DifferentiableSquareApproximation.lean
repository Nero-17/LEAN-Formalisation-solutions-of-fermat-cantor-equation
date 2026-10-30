import LambdaCantor.Classical.GeneralIsolation
import LambdaCantor.Classical.DifferentiableRemainder

noncomputable section
namespace LambdaCantor.Classical

theorem continuousLinearMap_coordinates (derivative : (ℝ × ℝ) →L[ℝ] ℝ)
    (direction : ℝ × ℝ) :
    derivative direction = derivative (1,0) * direction.1 + derivative (0,1) * direction.2 := by
  have decomposition : direction = direction.1 • (1,0) + direction.2 • (0,1) := by
    ext <;> simp
  calc
    derivative direction = derivative (direction.1 • (1,0) + direction.2 • (0,1)) :=
      congrArg derivative decomposition
    _ = derivative (1,0) * direction.1 + derivative (0,1) * direction.2 := by
      rw [map_add, map_smul, map_smul]
      simp only [smul_eq_mul, mul_comm]

/-- Actual differentiability supplies the normalized errors used in the geometric
exclusion argument, uniformly over all tails in a retained square. -/
theorem differentiable_square_approximation (function : ℝ → ℝ → ℝ)
    (continuous : ContinuousOn (fun point : ℝ × ℝ => function point.1 point.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : CoordinateBounds function horizontalLower horizontalUpper verticalLower verticalUpper)
    (first_gap : verticalUpper ≤ horizontalLower)
    (middle_gap : horizontalUpper ≤ 3 * verticalLower)
    (a b horizontal vertical : ℝ) (vertical_positive : 0 < vertical)
    (derivative : (ℝ × ℝ) →L[ℝ] ℝ)
    (differentiable : HasFDerivAt (fun point : ℝ × ℝ => function point.1 point.2) derivative (a,b))
    (derivative_formula : ∀ direction, derivative direction =
      horizontal * direction.1 + vertical * direction.2)
    (error : ℝ) (error_positive : 0 < error) :
    ∃ radius > 0, ∀ u v tailA tailB side : ℝ,
      tailA ∈ Set.Icc (0 : ℝ) 1 → tailB ∈ Set.Icc (0 : ℝ) 1 →
      0 < side → side < radius →
      SquareApproximation function u v a b tailA tailB side (horizontal / vertical) error := by
  obtain ⟨radius, radius_positive, estimate⟩ := differentiable_uniform_scaled_remainder
    (fun point : ℝ × ℝ => function point.1 point.2) derivative (a,b) differentiable
    (2 * vertical * error) (by positivity)
  refine ⟨radius, radius_positive, ?_⟩
  intro u v tailA tailB side tailA_bounds tailB_bounds side_positive side_small
  apply squareApproximation_of_coordinateBounds function continuous _ _ _ _ bounds first_gap middle_gap
    u v a b tailA tailB side (horizontal / vertical) error (2 * side * vertical)
    error_positive.le (by positivity)
  intro x y x_bounds y_bounds
  have direction_bound : ‖(x-tailA, y-tailB)‖ ≤ (1 : ℝ) := by
    change max |x-tailA| |y-tailB| ≤ 1
    apply max_le <;> apply abs_le.mpr <;> constructor <;>
      linarith [x_bounds.1, x_bounds.2, y_bounds.1, y_bounds.2,
        tailA_bounds.1, tailA_bounds.2, tailB_bounds.1, tailB_bounds.2]
  have remainder := estimate side side_positive side_small (x-tailA,y-tailB) direction_bound
  rw [derivative_formula] at remainder
  change |function (a + side*(x-tailA)) (b + side*(y-tailB)) - function a b -
    (horizontal * (side*(x-tailA)) + vertical * (side*(y-tailB)))| / side ≤
      2 * vertical * error at remainder
  have equality :
      (function (a + side*(x-tailA)) (b + side*(y-tailB)) - function a b) /
          (2 * side * vertical) -
        ((horizontal / vertical * x + y) / 2 - (horizontal / vertical * tailA + tailB) / 2) =
      (function (a + side*(x-tailA)) (b + side*(y-tailB)) - function a b -
        (horizontal * (side*(x-tailA)) + vertical * (side*(y-tailB)))) /
          (2 * side * vertical) := by
    field_simp [ne_of_gt side_positive, ne_of_gt vertical_positive]
    <;> ring
  rw [equality, abs_div, abs_of_pos (by positivity : 0 < 2 * side * vertical)]
  apply (div_le_iff₀ (by positivity : 0 < 2 * side * vertical)).mpr
  have cleared := (div_le_iff₀ side_positive).mp remainder
  nlinarith

end LambdaCantor.Classical
