import LambdaCantor.Last.AnalyticIsolatedPhases

noncomputable section
namespace LambdaCantor.Last

theorem above_critical_phase_overlap {ratio : ℝ}
    (above_critical : (Real.sqrt 3-1)/2 < ratio) (less_half : ratio < 1/2) :
    1/ratio-1-ratio < ratio/(1-2*ratio) := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have positive : 0 < ratio := by nlinarith
  have critical_positive : 0 < (Real.sqrt 3-1)/2 := by nlinarith
  have critical_equation : 2*((Real.sqrt 3-1)/2)^2+2*((Real.sqrt 3-1)/2)=1 := by nlinarith
  have polynomial_positive : 0 < 2*ratio^2+2*ratio-1 := by
    nlinarith [mul_pos (sub_pos.mpr above_critical)
      (show 0 < ratio+(Real.sqrt 3-1)/2+1 by positivity)]
  have numerator_positive : 0 < 3*ratio-1-2*ratio^3 := by
    nlinarith [mul_pos polynomial_positive (show 0 < 1-ratio by linarith)]
  have left_eq : 1/ratio-1-ratio = (1-ratio-ratio^2)/ratio := by
    field_simp [positive.ne']
  rw [left_eq]
  apply (div_lt_div_iff₀ positive (show 0 < 1-2*ratio by linarith)).mpr
  nlinarith

/-- Above the critical contraction every normalized phase is covered, with
no arithmetic exclusion hypothesis. This is the coverage needed for actual
isolated-point classification, before field membership is known. -/
theorem above_critical_normalized_phase_cases {ratio slope : ℝ}
    (above_critical : (Real.sqrt 3-1)/2 < ratio) (less_half : ratio < 1/2)
    (normalized : 1 ≤ slope ∧ slope < 1/ratio) :
    SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope ∨
      SmallPeriodicityPhase ratio (1/(ratio*slope)) := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have positive : 0 < ratio := by nlinarith
  have above_third : (1/3 : ℝ) < ratio := by nlinarith
  have complement_positive : 0 < 1-2*ratio := by linarith
  have middle_positive : 0 < 1-ratio-ratio^2 := by nlinarith
  have slope_positive : 0 < slope := by linarith [normalized.1]
  have overlap := above_critical_phase_overlap above_critical less_half
  by_cases small : slope < ratio/(1-2*ratio)
  · exact Or.inl ⟨normalized.1, by simpa [mul_comm] using (lt_div_iff₀ complement_positive).mp small,
      critical_ratio_small_triple_margin above_critical.le less_half normalized.1⟩
  · have threshold_lower : 1 < ratio/(1-2*ratio) := by
      apply (lt_div_iff₀ complement_positive).mpr
      linarith
    have above_lower : 1/ratio-1-ratio < slope := overlap.trans_le (le_of_not_gt small)
    by_cases middle : slope < 1/(1-ratio-ratio^2)
    · right
      left
      refine ⟨threshold_lower.trans_le (le_of_not_gt small), ?_, ?_⟩
      · have inequality : 1/ratio < slope+1+ratio := by linarith
        nlinarith [(div_lt_iff₀ positive).mp inequality]
      · simpa [mul_comm] using (lt_div_iff₀ middle_positive).mp middle
    · right
      right
      have inverse_lower : 1 ≤ 1/(ratio*slope) := by
        apply (le_div_iff₀ (mul_pos positive slope_positive)).mpr
        nlinarith [(lt_div_iff₀ positive).mp normalized.2]
      have inverse_upper : 1/(ratio*slope) ≤ 1/ratio-1-ratio := by
        have product_lower := (div_le_iff₀ middle_positive).mp (le_of_not_gt middle)
        have right_eq : 1/ratio-1-ratio = (1-ratio-ratio^2)/ratio := by
          field_simp [positive.ne']
        rw [right_eq]
        apply (div_le_div_iff₀ (mul_pos positive slope_positive) positive).mpr
        nlinarith [mul_le_mul_of_nonneg_left product_lower positive.le]
      exact ⟨inverse_lower, by simpa [mul_comm] using
          (lt_div_iff₀ complement_positive).mp (inverse_upper.trans_lt overlap),
        critical_ratio_small_triple_margin above_critical.le less_half inverse_lower⟩

end LambdaCantor.Last
