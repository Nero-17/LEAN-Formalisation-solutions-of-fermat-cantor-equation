import LambdaCantor.Last.AnalyticIsolatedPhases

noncomputable section
namespace LambdaCantor.Last

/-- At c the only normalized phases not already covered by the open
periodicity arguments are exactly 1+c and 2. -/
theorem critical_normalized_isolation_phase_cases {ratio slope : ℝ}
    (critical : ratio = (Real.sqrt 3-1)/2) (normalized : 1 ≤ slope ∧ slope < 1/ratio) :
    SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope ∨
      SmallPeriodicityPhase ratio (1/(ratio*slope)) ∨ slope = 1+ratio ∨ slope = 2 := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have positive : 0 < ratio := by rw [critical]; nlinarith
  have less_half : ratio < 1/2 := by rw [critical]; nlinarith
  have critical_equation : 2*ratio^2+2*ratio = 1 := by rw [critical]; nlinarith
  have slope_positive : 0 < slope := by linarith [normalized.1]
  have middle_coefficient : 1-ratio-ratio^2 = (1/2 : ℝ) := by nlinarith
  have threshold_identity : ratio/(1-2*ratio) = 1+ratio := by
    apply (div_eq_iff (show 1-2*ratio ≠ 0 by linarith)).mpr
    nlinarith
  rcases lt_trichotomy slope (1+ratio) with small | boundary | above
  · left
    refine ⟨normalized.1, ?_, critical_ratio_small_triple_margin critical.ge less_half normalized.1⟩
    simpa [mul_comm] using
      (lt_div_iff₀ (show 0 < 1-2*ratio by linarith)).mp
        (show slope < ratio/(1-2*ratio) by simpa [threshold_identity] using small)
  · exact Or.inr (Or.inr (Or.inr (Or.inl boundary)))
  · rcases lt_trichotomy slope 2 with middle | boundary | large
    · right
      left
      refine ⟨by linarith, ?_, ?_⟩
      · rw [middle_coefficient]
        nlinarith [mul_pos positive (sub_pos.mpr above)]
      · rw [middle_coefficient]
        linarith
    · exact Or.inr (Or.inr (Or.inr (Or.inr boundary)))
    · right
      right
      left
      have inverse_lower : 1 ≤ 1/(ratio*slope) := by
        apply (le_div_iff₀ (mul_pos positive slope_positive)).mpr
        nlinarith [(lt_div_iff₀ positive).mp normalized.2]
      refine ⟨inverse_lower, ?_,
        critical_ratio_small_triple_margin critical.ge less_half inverse_lower⟩
      have numerator_bound : 1-2*ratio < ratio*(ratio*slope) := by
        nlinarith [mul_pos (sq_pos_of_pos positive) (sub_pos.mpr large)]
      simpa only [div_eq_mul_inv, mul_inv_rev, one_mul, mul_assoc] using
        (div_lt_iff₀ (mul_pos positive slope_positive)).mpr numerator_bound

theorem critical_inverse_two_phase {ratio : ℝ} (critical : ratio = (Real.sqrt 3-1)/2) :
    1/(ratio*2) = 1+ratio := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have positive : 0 < ratio := by rw [critical]; nlinarith
  apply (div_eq_iff (mul_ne_zero positive.ne' (by norm_num))).mpr
  rw [critical]
  nlinarith

end LambdaCantor.Last
