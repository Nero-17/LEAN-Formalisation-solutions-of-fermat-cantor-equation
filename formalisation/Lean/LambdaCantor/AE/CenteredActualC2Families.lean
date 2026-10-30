import LambdaCantor.AE.CenteredFullSecondLimit
import LambdaCantor.AE.CenteredRoots

noncomputable section
open Filter
open scoped Topology

namespace LambdaCantor.AE

/-- The depth sequences and all derivative constants are chosen once.
Every fixed enlargement of the root window eventually satisfies the same
first and complete second derivative bounds. The eventual threshold may
depend on the enlargement, as needed for the actual freezing intervals. -/
theorem irrational_centered_C2_families_expanded {exponent center lower upper : ℝ}
    (irrational : Irrational exponent) (exponent_greater_one : 1 < exponent)
    (lower_positive : 0 < lower) (center_lower : lower < center) (center_upper : center < upper)
    (upper_less_one : upper < 1) :
    ∃ horizontalDepth verticalDepth : ℕ → ℕ, ∃ width slope firstBound secondBound : ℝ,
      0 < width ∧ 0 < slope ∧ 0 < firstBound ∧ 0 < secondBound ∧
      (∀ index, index ≤ horizontalDepth index ∧ index ≤ verticalDepth index ∧ 2 ≤ verticalDepth index) ∧
      (∀ index, |(verticalDepth index : ℝ)-exponent*horizontalDepth index +
        Real.log exponent/Real.log center| < (center^index)^2 ∧
        (verticalDepth index : ℝ)^2*upper^verticalDepth index < (center^index)^3) ∧
      ∀ expansion : ℝ, 0 ≤ expansion → ∀ᶠ index : ℕ in atTop,
        (∀ digits : ℕ → Bool × Bool, ∃! root : ℝ,
          root ∈ Set.Icc (center-width*center^index) (center+width*center^index) ∧
            centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index digits root = 0) ∧
        (∀ digits ratio, ratio ∈ Set.Icc lower upper → |ratio-center| ≤ (width+expansion)*center^index →
          deriv (centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index digits) ratio ≤ -slope ∧
          |deriv (centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index digits) ratio| ≤ firstBound ∧
          |centeredNormalizedSecond exponent (horizontalDepth index) (verticalDepth index) index digits ratio| ≤ secondBound) := by
  have center_positive := lower_positive.trans center_lower
  have center_less_one := center_upper.trans upper_less_one
  obtain ⟨horizontalDepth, verticalDepth, depth, choices, remainder⟩ :=
    centered_actual_C2_depth_sequences irrational exponent_greater_one center_positive center_less_one
      lower_positive (center_lower.le.trans center_upper.le) upper_less_one
  obtain ⟨width, width_positive, roots⟩ := centered_depths_have_unique_roots exponent_greater_one
    lower_positive center_lower center_upper upper_less_one horizontalDepth verticalDepth
    (fun index => (depth index).2.1) (fun index => (depth index).2.2)
    (fun index => (choices index).1.le) (fun index => (choices index).2.le)
    (fun ratios ratios_mem digits => (remainder ratios ratios_mem digits).2.1)
  have discrepancy_positive := centered_resonance_exponent_positive exponent_greater_one center_positive center_less_one
  let slope := exponent*(-Real.log exponent/Real.log center)*center^(-Real.log exponent/Real.log center-1)/2
  let firstBound := |-exponent*(-Real.log exponent/Real.log center)*center^(-Real.log exponent/Real.log center-1)|+1
  let secondBound := |-exponent*(-Real.log exponent/Real.log center)*
    (-Real.log exponent/Real.log center-1)*center^(-Real.log exponent/Real.log center-2)|+1
  have exponent_positive : 0 < exponent := by linarith
  have slope_positive : 0 < slope := by dsimp [slope]; positivity
  have first_positive : 0 < firstBound := by dsimp [firstBound]; positivity
  have second_positive : 0 < secondBound := by dsimp [secondBound]; positivity
  refine ⟨horizontalDepth, verticalDepth, width, slope, firstBound, secondBound,
    width_positive, slope_positive, first_positive, second_positive, depth, choices, ?_⟩
  intro expansion expansion_nonnegative
  have negative := centered_uniform_negative_derivative exponent_greater_one center_positive center_less_one lower_positive
    ⟨center_lower.le, center_upper.le⟩ upper_less_one (add_nonneg width_positive.le expansion_nonnegative) horizontalDepth verticalDepth
    (fun index => (depth index).2.1) (fun index => (choices index).1.le)
    (fun ratios ratios_mem digits => (remainder ratios ratios_mem digits).2.1)
  have first := centered_uniform_derivative_upper_bound center_positive center_less_one lower_positive
    ⟨center_lower.le, center_upper.le⟩ upper_less_one (add_nonneg width_positive.le expansion_nonnegative) horizontalDepth verticalDepth
    (fun index => (depth index).2.1) (fun index => (choices index).1.le)
    (fun ratios ratios_mem digits => (remainder ratios ratios_mem digits).2.1)
  have second := centered_uniform_second_derivative_bound center_positive center_less_one lower_positive
    ⟨center_lower.le, center_upper.le⟩ upper_less_one (add_nonneg width_positive.le expansion_nonnegative) horizontalDepth verticalDepth
    (fun index => (choices index).1.le)
    (fun ratios ratios_mem digits => (remainder ratios ratios_mem digits).2.2)
  filter_upwards [roots, negative, first, second] with index roots negative first second
  refine ⟨roots, ?_⟩
  intro digits ratio ratio_mem distance_bound
  refine ⟨?_, first digits ratio ratio_mem distance_bound, second digits ratio ratio_mem distance_bound⟩
  have derivative_negative := negative digits ratio ratio_mem distance_bound
  dsimp [slope]
  linarith

/-- The original root-window interface is preserved as the zero-enlargement
specialization of the stronger freezing-window construction. -/
theorem irrational_centered_C2_families {exponent center lower upper : ℝ}
    (irrational : Irrational exponent) (exponent_greater_one : 1 < exponent)
    (lower_positive : 0 < lower) (center_lower : lower < center) (center_upper : center < upper)
    (upper_less_one : upper < 1) :
    ∃ horizontalDepth verticalDepth : ℕ → ℕ, ∃ width slope firstBound secondBound : ℝ,
      0 < width ∧ 0 < slope ∧ 0 < firstBound ∧ 0 < secondBound ∧
      (∀ index, index ≤ horizontalDepth index ∧ index ≤ verticalDepth index ∧ 2 ≤ verticalDepth index) ∧
      (∀ index, |(verticalDepth index : ℝ)-exponent*horizontalDepth index +
        Real.log exponent/Real.log center| < (center^index)^2 ∧
        (verticalDepth index : ℝ)^2*upper^verticalDepth index < (center^index)^3) ∧
      ∀ᶠ index : ℕ in atTop,
        (∀ digits : ℕ → Bool × Bool, ∃! root : ℝ,
          root ∈ Set.Icc (center-width*center^index) (center+width*center^index) ∧
            centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index digits root = 0) ∧
        (∀ digits ratio, ratio ∈ Set.Icc lower upper → |ratio-center| ≤ width*center^index →
          deriv (centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index digits) ratio ≤ -slope ∧
          |deriv (centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index digits) ratio| ≤ firstBound ∧
          |centeredNormalizedSecond exponent (horizontalDepth index) (verticalDepth index) index digits ratio| ≤ secondBound) := by
  obtain ⟨horizontalDepth, verticalDepth, width, slope, firstBound, secondBound,
    width_positive, slope_positive, first_positive, second_positive, depth, choices, estimates⟩ :=
    irrational_centered_C2_families_expanded irrational exponent_greater_one lower_positive center_lower center_upper upper_less_one
  refine ⟨horizontalDepth, verticalDepth, width, slope, firstBound, secondBound,
    width_positive, slope_positive, first_positive, second_positive, depth, choices, ?_⟩
  simpa only [add_zero] using estimates 0 (by norm_num)

end LambdaCantor.AE
