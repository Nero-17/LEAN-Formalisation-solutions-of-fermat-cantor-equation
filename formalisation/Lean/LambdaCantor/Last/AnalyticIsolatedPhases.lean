import LambdaCantor.Last.AnalyticIsolatedOrbit
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace LambdaCantor.Last

theorem critical_ratio_small_triple_margin {ratio slope : ℝ}
    (above_critical : (Real.sqrt 3-1)/2 ≤ ratio) (less_half : ratio < 1/2)
    (slope_lower : 1 ≤ slope) :
    1-ratio < ratio*(1-ratio+ratio^2+slope) := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have rational_lower : (4/11 : ℝ) < ratio := by nlinarith
  have ratio_positive : 0 < ratio := by linarith
  have bracket_nonnegative : 0 ≤ 3-ratio-4/11+ratio^2+ratio*(4/11)+(4/11)^2 := by
    nlinarith [sq_nonneg ratio]
  have polynomial_positive : 0 < 3*ratio-ratio^2+ratio^3-1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr rational_lower.le) bracket_nonnegative]
  nlinarith [mul_le_mul_of_nonneg_left slope_lower ratio_positive.le]

theorem critical_ratio_phase_overlap {ratio : ℝ}
    (above_critical : (Real.sqrt 3-1)/2 ≤ ratio) (less_half : ratio < 1/2) :
    1/ratio-1-ratio ≤ ratio/(1-2*ratio) := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have ratio_positive : 0 < ratio := by nlinarith
  have critical_positive : 0 < (Real.sqrt 3-1)/2 := by nlinarith
  have critical_square : 2*((Real.sqrt 3-1)/2)^2+2*((Real.sqrt 3-1)/2)=1 := by nlinarith
  have polynomial_nonnegative : 0 ≤ 2*ratio^2+2*ratio-1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr above_critical)
      (show 0 ≤ ratio+(Real.sqrt 3-1)/2+1 by positivity)]
  have numerator_nonnegative : 0 ≤ 3*ratio-1-2*ratio^3 := by
    nlinarith [mul_nonneg polynomial_nonnegative (show 0 ≤ 1-ratio by linarith)]
  have denominator_positive : 0 < 1-2*ratio := by linarith
  have left_eq : 1/ratio-1-ratio = (1-ratio-ratio^2)/ratio := by
    field_simp [ratio_positive.ne']
  rw [left_eq]
  apply (div_le_div_iff₀ ratio_positive denominator_positive).mpr
  nlinarith

/-- Field exclusion removes the two boundary phases even at the critical
contraction. After at most the prescribed coordinate/depth exchange, every
normalized tangent belongs to one of the open periodicity intervals. -/
theorem normalized_external_slope_in_periodicity_phase {ratio slope : ℝ}
    (above_critical : (Real.sqrt 3-1)/2 ≤ ratio) (less_half : ratio < 1/2)
    (normalized : 1 ≤ slope ∧ slope < 1/ratio)
    (outside : slope ∉ parameterField ratio) :
    SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope ∨
      SmallPeriodicityPhase ratio (1/(ratio*slope)) := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have positive : 0 < ratio := by nlinarith
  have complement_positive : 0 < 1-2*ratio := by linarith
  have middle_denominator_positive : 0 < 1-ratio-ratio^2 := by nlinarith
  have slope_positive : 0 < slope := by linarith [normalized.1]
  have threshold_mem : ratio/(1-2*ratio) ∈ parameterField ratio :=
    (parameterField ratio).div_mem (ratio_mem_parameterField ratio)
      ((parameterField ratio).sub_mem (parameterField ratio).one_mem
        ((parameterField ratio).mul_mem (by norm_num)
          (ratio_mem_parameterField ratio)))
  have threshold_ne : slope ≠ ratio/(1-2*ratio) := by
    intro equal
    apply outside
    rw [equal]
    exact threshold_mem
  have overlap := critical_ratio_phase_overlap above_critical less_half
  by_cases small : slope < ratio/(1-2*ratio)
  · left
    exact ⟨normalized.1, by simpa [mul_comm] using (lt_div_iff₀ complement_positive).mp small,
      critical_ratio_small_triple_margin above_critical less_half normalized.1⟩
  · have above_threshold : ratio/(1-2*ratio) < slope := lt_of_le_of_ne (le_of_not_gt small) threshold_ne.symm
    by_cases middle : slope < 1/(1-ratio-ratio^2)
    · right
      left
      have slope_gt_one : 1 < slope := lt_of_le_of_ne normalized.1 (by
        intro equal
        exact outside (equal ▸ (parameterField ratio).one_mem))
      refine ⟨slope_gt_one, ?_, ?_⟩
      · have lower := overlap.trans_lt above_threshold
        have lower' : 1/ratio < slope+1+ratio := by linarith
        nlinarith [(div_lt_iff₀ positive).mp lower']
      · simpa [mul_comm] using (lt_div_iff₀ middle_denominator_positive).mp middle
    · right
      right
      have inverse_lower : 1 ≤ 1/(ratio*slope) := by
        apply (le_div_iff₀ (mul_pos positive slope_positive)).mpr
        have product_lt := (lt_div_iff₀ positive).mp normalized.2
        nlinarith
      have inverse_outside : 1/(ratio*slope) ∉ parameterField ratio := by
        simpa [one_div] using inv_not_mem_parameterField
          (mul_not_mem_parameterField (ratio_mem_parameterField ratio) positive.ne' outside)
      have inverse_le : 1/(ratio*slope) ≤ 1/ratio-1-ratio := by
        have product_lower := (div_le_iff₀ middle_denominator_positive).mp (le_of_not_gt middle)
        have right_eq : 1/ratio-1-ratio = (1-ratio-ratio^2)/ratio := by
          field_simp [positive.ne']
        rw [right_eq]
        apply (div_le_div_iff₀ (mul_pos positive slope_positive) positive).mpr
        nlinarith [mul_le_mul_of_nonneg_left product_lower positive.le]
      have inverse_small : 1/(ratio*slope) < ratio/(1-2*ratio) :=
        lt_of_le_of_ne (inverse_le.trans overlap) (by
          intro equal
          apply inverse_outside
          rw [equal]
          exact threshold_mem)
      exact ⟨inverse_lower, by simpa [mul_comm] using (lt_div_iff₀ complement_positive).mp inverse_small,
        critical_ratio_small_triple_margin above_critical less_half inverse_lower⟩

end LambdaCantor.Last
