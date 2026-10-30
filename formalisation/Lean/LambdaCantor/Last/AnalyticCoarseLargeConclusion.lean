import LambdaCantor.Last.AnalyticCoarseLargeSelection
import LambdaCantor.Last.AnalyticCoarseLargeCircle
import LambdaCantor.Last.AnalyticCoarseSecantMajorant

noncomputable section
namespace LambdaCantor.Last

/-- Every actual periodic empty interval in α log(outer Cλ) is shorter than
its logarithmic hull width for α≥20. All scale selection, secant displacement,
linear circle geometry, and rational comparison steps are invoked as proved
theorems, with no circle-gap or perturbation conclusion assumed. -/
theorem coarse_large_exponent_circle_gaps_lt_hull {exponent ratio left right : ℝ}
    (exponent_lower : 20 ≤ exponent) (ratio_lower : 183/500 ≤ ratio) (ratio_upper : ratio < 1/2)
    (empty_arc : ∀ coordinate ∈ outerCantor ratio, ∀ translate : ℤ,
      exponent*Real.log coordinate+(translate : ℝ)*(-Real.log ratio) ∉ Set.Ioo left right) :
    right-left < -Real.log (1-ratio) := by
  have ratio_positive : 0 < ratio := by linarith
  have ratio_less_one : ratio < 1 := by linarith
  have complement_positive : 0 < 1-ratio := by linarith
  have period_positive : 0 < -Real.log ratio := neg_pos.mpr (Real.log_neg ratio_positive ratio_less_one)
  have basic_bounds := coarse_log_hull_period_bounds ratio_lower ratio_upper
  obtain ⟨depth, depth_positive, scale_lower, next_scale_small, scale_upper⟩ :=
    exists_large_secant_scale_of_twenty exponent_lower ratio_lower ratio_upper
  have scale_identity : largeSecantScale exponent ratio (-Real.log ratio) depth*(-Real.log ratio) =
      exponent*Real.log (1+ratio^depth/(1-ratio)) := by
    unfold largeSecantScale
    exact div_mul_cancel₀ _ period_positive.ne'
  have scale_numeric_upper : largeSecantScale exponent ratio (-Real.log ratio) depth ≤ 11/4 := by
    have reciprocal_bound : 1/ratio < (11/4 : ℝ) :=
      (div_lt_iff₀ ratio_positive).mpr (by nlinarith)
    exact (scale_upper.trans reciprocal_bound).le
  have empty_copy : ∀ coordinate ∈ cantorSet ratio, ∀ translate : ℤ,
      largeLogarithmicCopy exponent ratio depth coordinate+(translate : ℝ)*(-Real.log ratio) ∉
        Set.Ioo left right := by
    intro coordinate membership translate
    obtain ⟨outer_coordinate, outer_membership, representation⟩ :=
      large_logarithmic_copy_mem_outer_image (exponent := exponent) (depth := depth)
        ratio_positive ratio_less_one
        (by omega) membership
    rw [← representation]
    exact empty_arc outer_coordinate outer_membership translate
  have copy_bound := large_logarithmic_copy_circle_gap_bound depth (by linarith)
    (show (1/3 : ℝ) ≤ ratio by linarith) ratio_upper period_positive
    scale_lower scale_upper scale_identity empty_copy
  have period_bound : -Real.log ratio ≤ (503/500 : ℝ) := by linarith [basic_bounds.2.1]
  have error_bound := coarse_secant_error_majorant exponent_lower period_bound
    scale_lower scale_numeric_upper
    (div_nonneg (pow_nonneg ratio_positive.le _) complement_positive.le) scale_identity
  have circle_nonnegative : 0 ≤ max (1-2*ratio)
      (min (largeSecantScale exponent ratio (-Real.log ratio) depth*(1-2*ratio))
        (2-largeSecantScale exponent ratio (-Real.log ratio) depth)) :=
    (show 0 ≤ 1-2*ratio by linarith).trans (le_max_left _ _)
  have period_comparison := mul_le_mul_of_nonneg_right period_bound circle_nonnegative
  have total_comparison := coarse_circle_secant_total_lt ratio_lower scale_lower scale_numeric_upper
  linarith [basic_bounds.1]

/-- The large-exponent branch of the actual strict logarithmic hull linkage.
The selected coordinate belongs to the real outer Cantor set. -/
theorem coarse_large_exponent_strict_link {exponent ratio : ℝ}
    (exponent_lower : 20 ≤ exponent) (ratio_lower : 183/500 ≤ ratio) (ratio_upper : ratio < 1/2) :
    ∃ coordinate ∈ outerCantor ratio, ∃ translate : ℤ,
      exponent*Real.log coordinate ∈ Set.Ioo
        (Real.log exponent-(translate : ℝ)*(-Real.log ratio)+Real.log (1-ratio))
        (Real.log exponent-(translate : ℝ)*(-Real.log ratio)) := by
  classical
  have exists_translated : ∃ coordinate ∈ outerCantor ratio, ∃ translate : ℤ,
      exponent*Real.log coordinate+(translate : ℝ)*(-Real.log ratio) ∈
        Set.Ioo (Real.log exponent+Real.log (1-ratio)) (Real.log exponent) := by
    by_contra failure
    push_neg at failure
    have impossible := coarse_large_exponent_circle_gaps_lt_hull exponent_lower ratio_lower ratio_upper failure
    linarith
  obtain ⟨coordinate, membership, translate, inside⟩ := exists_translated
  refine ⟨coordinate, membership, translate, ?_⟩
  constructor <;> linarith [inside.1, inside.2]

end LambdaCantor.Last
