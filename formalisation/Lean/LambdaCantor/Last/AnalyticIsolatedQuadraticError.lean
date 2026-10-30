import LambdaCantor.Last.LocalSource
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open scoped NNReal
open scoped Topology NNReal
namespace LambdaCantor.Last

/-- A C² function has exponentially small normalized cylinder errors, at
the precise rate required by the boundary shadowing argument. This strengthens
the qualitative strict-derivative cylinder estimate by keeping its scale. -/
theorem c2_derivative_cylinder_error {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1)
    {function : (ℝ × ℝ) → ℝ} {linear : (ℝ × ℝ) →L[ℝ] ℝ} {point : ℝ × ℝ}
    (smooth : ContDiffAt ℝ 2 function point) (derivative : HasFDerivAt function linear point) :
    ∃ coefficient : ℝ≥0, 0 < coefficient ∧ ∃ cutoff : ℕ,
      ∀ word : List (Bool × Bool), cutoff ≤ word.length → point ∈ wordCylinder ratio word →
        LipschitzOnWith (coefficient*⟨ratio^word.length, pow_nonneg positive.le _⟩)
          (fun value => function value-linear value) (wordCylinder ratio word) := by
  have derivative_smooth : ContDiffAt ℝ 1 (fderiv ℝ function) point :=
    smooth.fderiv_right (by norm_num)
  obtain ⟨constant, neighbourhood, neighbourhood_mem, derivative_lipschitz⟩ :=
    derivative_smooth.exists_lipschitzOnWith
  have differentiable_near : ∀ᶠ value in 𝓝 point, DifferentiableAt ℝ function value :=
    (smooth.eventually (by norm_num)).mono (fun _ hypothesis => hypothesis.differentiableAt (by norm_num))
  obtain ⟨radius, radius_positive, ball_subset⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem neighbourhood_mem differentiable_near)
  obtain ⟨cutoff, scale_small⟩ := exists_pow_lt_of_lt_one (half_pos radius_positive) less_one
  let coefficient : ℝ≥0 := 2*constant+1
  refine ⟨coefficient, by dsimp [coefficient]; positivity, cutoff, ?_⟩
  intro word depth_lower point_in_word
  have scale_positive : 0 < ratio^word.length := pow_pos positive _
  have scale_bound : ratio^word.length ≤ ratio^cutoff :=
    pow_le_pow_of_le_one positive.le less_one.le depth_lower
  have radius_bound : 2*ratio^word.length < radius := by linarith
  have local_subset : Metric.ball point (2*ratio^word.length) ⊆
      neighbourhood ∩ {value | DifferentiableAt ℝ function value} := by
    intro value value_near
    exact ball_subset (Metric.mem_ball.mpr ((Metric.mem_ball.mp value_near).trans radius_bound))
  have point_in_neighbourhood : point ∈ neighbourhood := mem_of_mem_nhds neighbourhood_mem
  have ball_lipschitz : LipschitzOnWith
      (coefficient*⟨ratio^word.length, pow_nonneg positive.le _⟩)
      (fun value => function value-linear value) (Metric.ball point (2*ratio^word.length)) := by
    apply (convex_ball point (2*ratio^word.length)).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun value membership =>
        (((local_subset membership).2.hasFDerivAt).sub linear.hasFDerivAt).hasFDerivWithinAt)
    intro value membership
    have difference_bound := derivative_lipschitz.dist_le_mul
      value (local_subset membership).1 point point_in_neighbourhood
    rw [dist_eq_norm, derivative.fderiv] at difference_bound
    have point_distance := Metric.mem_ball.mp membership
    have real_bound : ‖fderiv ℝ function value-linear‖ ≤
        (coefficient : ℝ)*ratio^word.length := by
      change ‖fderiv ℝ function value-linear‖ ≤ (2*(constant : ℝ)+1)*ratio^word.length
      nlinarith [mul_le_mul_of_nonneg_left point_distance.le constant.coe_nonneg]
    exact_mod_cast real_bound
  apply ball_lipschitz.mono
  intro value value_in_word
  apply Metric.mem_ball.mpr
  exact (wordCylinder_dist_le positive.le less_one word value_in_word point_in_word).trans_lt
    (by linarith)

end LambdaCantor.Last
