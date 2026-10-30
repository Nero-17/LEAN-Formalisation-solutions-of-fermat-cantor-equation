import LambdaCantor.Last.ReturnParameterPersistence
import LambdaCantor.Last.LocalSource

noncomputable section
open Filter
open scoped NNReal Topology
namespace LambdaCantor.Last

/-- Joint strict differentiability controls the actual moving cylinders.
The derivative in the spatial variables is kept fixed at the original
point. A single sufficiently deep entrance word then remains admissible
for all nearby contraction parameters. -/
theorem joint_strict_derivative_moving_cylinder_error
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1)
    (family : ℝ → (ℝ × ℝ) → ℝ) (point : ℝ × ℝ)
    (jointLinear : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ) (linear : (ℝ × ℝ) →L[ℝ] ℝ)
    (joint_derivative : HasStrictFDerivAt (fun value : ℝ × (ℝ × ℝ) => family value.1 value.2)
      jointLinear (ratio, point))
    (spatial_derivative : ∀ increment : ℝ × ℝ, jointLinear (0, increment) = linear increment)
    (bound : ℝ≥0) (bound_positive : 0 < bound) :
    ∃ minimumDepth : ℕ, ∀ word : List (Bool × Bool), minimumDepth ≤ word.length →
      point ∈ wordCylinder ratio word →
      ∀ᶠ perturbed in 𝓝 ratio, LipschitzOnWith bound
        (fun value => family perturbed value-linear value) (wordCylinder perturbed word) := by
  have joint_error := joint_derivative.sub jointLinear.hasStrictFDerivAt
  rw [sub_self] at joint_error
  obtain ⟨neighborhood, neighborhood_mem, error_lipschitz⟩ :=
    joint_error.exists_lipschitzOnWith_of_nnnorm_lt bound (by simpa using bound_positive)
  obtain ⟨radius, radius_positive, ball_subset⟩ := Metric.mem_nhds_iff.mp neighborhood_mem
  obtain ⟨minimumDepth, scale_small⟩ :=
    exists_pow_lt_of_lt_one (show 0 < radius/4 by positivity) less_one
  refine ⟨minimumDepth, ?_⟩
  intro word depth_lower point_in_word
  have original_scale_small : ratio^word.length < radius/4 :=
    (pow_le_pow_of_le_one positive.le less_one.le depth_lower).trans_lt scale_small
  have original_corner : wordMap ratio word 0 ∈ wordCylinder ratio word :=
    ⟨0, ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩, rfl⟩
  have original_corner_distance : dist (wordMap ratio word 0) point < radius/4 :=
    (wordCylinder_dist_le positive.le less_one word original_corner point_in_word).trans_lt original_scale_small
  have scale_eventual : ∀ᶠ perturbed in 𝓝 ratio, perturbed^word.length < radius/4 :=
    (continuousAt_id.pow word.length).eventually_lt continuousAt_const original_scale_small
  have corner_eventual : ∀ᶠ perturbed in 𝓝 ratio,
      dist (wordMap perturbed word 0) (wordMap ratio word 0) < radius/4 :=
    (continuous_wordMap_zero_parameter word).continuousAt.eventually
      (Metric.ball_mem_nhds _ (show 0 < radius/4 by positivity))
  have parameter_eventual : ∀ᶠ perturbed in 𝓝 ratio, dist perturbed ratio < radius/4 :=
    Metric.ball_mem_nhds ratio (show 0 < radius/4 by positivity)
  filter_upwards [scale_eventual, corner_eventual, parameter_eventual,
    lt_mem_nhds positive, gt_mem_nhds less_one] with perturbed scale_close corner_close parameter_close
      perturbed_positive perturbed_less_one
  have in_neighborhood : ∀ value ∈ wordCylinder perturbed word,
      (perturbed, value) ∈ neighborhood := by
    intro value membership
    apply ball_subset
    apply Metric.mem_ball.mpr
    rw [Prod.dist_eq]
    change max (dist perturbed ratio) (dist value point) < radius
    apply max_lt (show dist perturbed ratio < radius by linarith)
    have moving_corner : wordMap perturbed word 0 ∈ wordCylinder perturbed word :=
      ⟨0, ⟨zero_mem_cantorSet perturbed, zero_mem_cantorSet perturbed⟩, rfl⟩
    have to_corner := (wordCylinder_dist_le perturbed_positive.le perturbed_less_one word
      membership moving_corner).trans_lt scale_close
    have triangle := dist_triangle value (wordMap perturbed word 0) point
    have triangle_corner := dist_triangle (wordMap perturbed word 0) (wordMap ratio word 0) point
    linarith
  apply LipschitzOnWith.of_dist_le_mul
  intro first first_mem second second_mem
  have error_bound := error_lipschitz.dist_le_mul
    (perturbed, first) (in_neighborhood first first_mem)
    (perturbed, second) (in_neighborhood second second_mem)
  have linear_difference : jointLinear (perturbed, first)-jointLinear (perturbed, second) =
      linear first-linear second := by
    rw [← map_sub]
    have increments : (perturbed, first)-(perturbed, second) = (0, first-second) := by
      ext <;> simp
    rw [increments, spatial_derivative, map_sub]
  have error_difference :
      (family perturbed first-jointLinear (perturbed, first))-
          (family perturbed second-jointLinear (perturbed, second)) =
        (family perturbed first-linear first)-(family perturbed second-linear second) := by
    linarith
  change dist (family perturbed first-jointLinear (perturbed, first))
      (family perturbed second-jointLinear (perturbed, second)) ≤
    (bound : ℝ)*dist (perturbed, first) (perturbed, second) at error_bound
  rw [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg : 0 ≤ dist first second),
    Real.dist_eq, error_difference] at error_bound
  simpa only [Real.dist_eq] using error_bound

end LambdaCantor.Last
