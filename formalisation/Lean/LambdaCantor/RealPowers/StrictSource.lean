import LambdaCantor.Integer.GoodSlopeReturnAdapter
import LambdaCantor.Classical.GeneralCover
import LambdaCantor.RealPowers.SourceTransformations
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open scoped NNReal Topology
namespace LambdaCantor.RealPowers
open Integer Last

/-- Ordered increment bounds give an absolute affine-error estimate in both
orders. This elementary step avoids any differentiability assumption on dust. -/
theorem absolute_increment_error (function : ℝ → ℝ) (center error : ℝ)
    (bounds : ∀ first ∈ Set.Icc (0 : ℝ) 1, ∀ second ∈ Set.Icc (0 : ℝ) 1,
      first ≤ second →
      (center-error)*(second-first) ≤ function second-function first ∧
      function second-function first ≤ (center+error)*(second-first))
    (first second : ℝ) (first_mem : first ∈ Set.Icc (0 : ℝ) 1)
    (second_mem : second ∈ Set.Icc (0 : ℝ) 1) :
    |(function first-center*first)-(function second-center*second)| ≤
      error*|first-second| := by
  rcases le_total first second with ordered | ordered
  · have estimate := bounds first first_mem second second_mem ordered
    rw [abs_of_nonpos (sub_nonpos.mpr ordered), abs_le]
    constructor <;> nlinarith [estimate.1, estimate.2]
  · have estimate := bounds second second_mem first first_mem ordered
    rw [abs_of_nonneg (sub_nonneg.mpr ordered), abs_le]
    constructor <;> nlinarith [estimate.1, estimate.2]

/-- Partial-increment errors add in the sup product metric. The estimate is
on the whole square and therefore restricts to every retained Cantor cylinder. -/
theorem coordinate_error_lipschitz (function : ℝ → ℝ → ℝ)
    (slope horizontalError verticalError : ℝ)
    (horizontal_nonnegative : 0 ≤ horizontalError)
    (vertical_nonnegative : 0 ≤ verticalError)
    (bounds : Classical.CoordinateBounds function
      (slope/2-horizontalError) (slope/2+horizontalError)
      (1/2-verticalError) (1/2+verticalError)) :
    LipschitzOnWith ⟨horizontalError+verticalError, add_nonneg horizontal_nonnegative vertical_nonnegative⟩
      (fun point : ℝ × ℝ => function point.1 point.2-goodSlopeLinear slope point)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro first first_mem second second_mem
  have horizontal := absolute_increment_error (fun x => function x first.2)
    (slope/2) horizontalError
    (fun x hx y hy ordered => bounds.horizontal first.2 first_mem.2 x hx y hy ordered)
    first.1 second.1 first_mem.1 second_mem.1
  have vertical := absolute_increment_error (fun y => function second.1 y)
    (1/2) verticalError
    (fun x hx y hy ordered => bounds.vertical second.1 second_mem.1 x hx y hy ordered)
    first.2 second.2 first_mem.2 second_mem.2
  have horizontal_distance : |first.1-second.1| ≤ dist first second := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have vertical_distance : |first.2-second.2| ≤ dist first second := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  rw [Real.dist_eq, goodSlopeLinear_apply, goodSlopeLinear_apply]
  change |(function first.1 first.2-(slope*first.1+first.2)/2) -
      (function second.1 second.2-(slope*second.1+second.2)/2)| ≤
    (horizontalError+verticalError)*dist first second
  calc
    _ = |((function first.1 first.2-(slope/2)*first.1) -
          (function second.1 first.2-(slope/2)*second.1)) +
        ((function second.1 first.2-(1/2)*first.2) -
          (function second.1 second.2-(1/2)*second.2))| := by congr 1 <;> ring
    _ ≤ |(function first.1 first.2-(slope/2)*first.1) -
          (function second.1 first.2-(slope/2)*second.1)| +
        |(function second.1 first.2-(1/2)*first.2) -
          (function second.1 second.2-(1/2)*second.2)| := abs_add_le _ _
    _ ≤ horizontalError*|first.1-second.1|+verticalError*|first.2-second.2| :=
      add_le_add horizontal vertical
    _ ≤ (horizontalError+verticalError)*dist first second := by
      nlinarith [mul_le_mul_of_nonneg_left horizontal_distance horizontal_nonnegative,
        mul_le_mul_of_nonneg_left vertical_distance vertical_nonnegative]

/-- A fixed irrational affine slope supplies a uniform nonlinear source
criterion directly from strict returns. No perfectness assumption is needed. -/
theorem good_slope_uniform_source (slope : ℝ) (good : GoodSlope slope)
    (irrational : ∀ rational : ℚ, slope ≠ (rational : ℝ)) :
    ∃ epsilon > 0, ∃ neighborhood : Set ℝ,
      IsOpen neighborhood ∧ switchSet slope ⊆ neighborhood ∧
      ∀ function : ℝ → ℝ → ℝ, ∀ level : ℝ,
        Classical.CoordinateBounds function (slope/2-epsilon) (slope/2+epsilon)
          (1/2-epsilon) (1/2+epsilon) →
        level-function 0 0 ∈ neighborhood →
        0 < dimH {point : ℝ × ℝ | point ∈ cantorDust (1/3) ∧ function point.1 point.2=level} := by
  obtain ⟨threshold, positive, neighborhood, opened, contained, criterion⟩ :=
    good_slope_local_source_criterion slope good irrational
  refine ⟨threshold/4, by positivity, neighborhood, opened, contained, ?_⟩
  intro function level bounds corner
  have estimate := coordinate_error_lipschitz function slope (threshold/4) (threshold/4)
    (by positivity) (by positivity) bounds
  apply criterion (NNReal.mk (threshold/4+threshold/4) (by positivity))
    (by simpa only [NNReal.coe_mk] using (show threshold/4+threshold/4 < threshold by linarith))
    (fun point => function point.1 point.2) level []
  · apply estimate.mono
    intro point member
    rcases member with ⟨tail, tail_mem, equality⟩
    have point_mem : point ∈ cantorDust (1/3) := by
      change tail = point at equality
      rwa [← equality]
    exact ⟨cantorSet_subset_unitInterval (by norm_num) (by norm_num) point_mem.1,
      cantorSet_subset_unitInterval (by norm_num) (by norm_num) point_mem.2⟩
  · simpa using corner

/-- The same strict-return source criterion applies to the reciprocal
orientation by swapping the two actual coordinates. -/
theorem good_slope_uniform_source_swapped (slope : ℝ) (good : GoodSlope slope)
    (irrational : ∀ rational : ℚ, slope ≠ (rational : ℝ)) :
    ∃ epsilon > 0, ∃ neighborhood : Set ℝ,
      IsOpen neighborhood ∧ switchSet slope ⊆ neighborhood ∧
      ∀ function : ℝ → ℝ → ℝ, ∀ level : ℝ,
        Classical.CoordinateBounds function (1/2-epsilon) (1/2+epsilon)
          (slope/2-epsilon) (slope/2+epsilon) →
        level-function 0 0 ∈ neighborhood →
        0 < dimH {point : ℝ × ℝ | point ∈ cantorDust (1/3) ∧ function point.1 point.2=level} := by
  obtain ⟨epsilon, positive, neighborhood, opened, contained, criterion⟩ :=
    good_slope_uniform_source slope good irrational
  refine ⟨epsilon, positive, neighborhood, opened, contained, ?_⟩
  intro function level bounds corner
  apply positive_dimension_of_swapped_source (function := fun point : ℝ × ℝ => function point.1 point.2)
  apply criterion (fun x y => function y x) level
  · exact ⟨bounds.vertical, bounds.horizontal⟩
  · exact corner

end LambdaCantor.RealPowers

