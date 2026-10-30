import LambdaCantor.Last.PerfectBranching
import LambdaCantor.Last.OverlapCore

noncomputable section
namespace LambdaCantor.Last

theorem positiveLinear_level_strict_of_two_points {ratio slope level : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio < 1) (hslope : 0 < slope)
    {first second : ℝ × ℝ} (hfirst : first ∈ cantorDust ratio)
    (hsecond : second ∈ cantorDust ratio) (hdifferent : first ≠ second)
    (hfirst_level : positiveLinear slope first = level)
    (hsecond_level : positiveLinear slope second = level) :
    level ∈ Set.Ioo 0 (1 + slope) := by
  obtain ⟨hfirst_x0, hfirst_x1⟩ := cantorSet_subset_unitInterval hratio hless hfirst.1
  obtain ⟨hfirst_y0, hfirst_y1⟩ := cantorSet_subset_unitInterval hratio hless hfirst.2
  obtain ⟨hsecond_x0, hsecond_x1⟩ := cantorSet_subset_unitInterval hratio hless hsecond.1
  obtain ⟨hsecond_y0, hsecond_y1⟩ := cantorSet_subset_unitInterval hratio hless hsecond.2
  have hlevel := positiveLinear_mem_unit_hull hratio hless hslope.le hfirst
  rw [hfirst_level] at hlevel
  change first.1 + slope * first.2 = level at hfirst_level
  change second.1 + slope * second.2 = level at hsecond_level
  constructor
  · by_contra hnot_positive
    have hzero : level = 0 := le_antisymm (le_of_not_gt hnot_positive) hlevel.1
    have hfirst_x : first.1 = 0 := by nlinarith [mul_nonneg hslope.le hfirst_y0]
    have hsecond_x : second.1 = 0 := by nlinarith [mul_nonneg hslope.le hsecond_y0]
    have hfirst_y : first.2 = 0 :=
      (mul_eq_zero.mp (show slope * first.2 = 0 by linarith)).resolve_left hslope.ne'
    have hsecond_y : second.2 = 0 :=
      (mul_eq_zero.mp (show slope * second.2 = 0 by linarith)).resolve_left hslope.ne'
    exact hdifferent (Prod.ext (hfirst_x.trans hsecond_x.symm) (hfirst_y.trans hsecond_y.symm))
  · by_contra hnot_below
    have htop : level = 1 + slope := le_antisymm hlevel.2 (le_of_not_gt hnot_below)
    have hfirst_x : first.1 = 1 := by
      nlinarith [mul_le_mul_of_nonneg_left hfirst_y1 hslope.le]
    have hsecond_x : second.1 = 1 := by
      nlinarith [mul_le_mul_of_nonneg_left hsecond_y1 hslope.le]
    have hfirst_y : first.2 = 1 :=
      (mul_left_cancel₀ hslope.ne') (show slope * first.2 = slope * 1 by linarith)
    have hsecond_y : second.2 = 1 :=
      (mul_left_cancel₀ hslope.ne') (show slope * second.2 = slope * 1 by linarith)
    exact hdifferent (Prod.ext (hfirst_x.trans hsecond_x.symm) (hfirst_y.trans hsecond_y.symm))

theorem linearWordReturn_of_preimage {ratio slope level : ℝ} (hpositive : 0 < ratio)
    (word : List (Bool × Bool)) (tail : ℝ × ℝ)
    (hlevel : positiveLinear slope (wordMap ratio word tail) = level) :
    linearWordReturn ratio (positiveLinear slope) word level = positiveLinear slope tail := by
  have hrestriction : positiveLinear slope (wordMap ratio word tail) =
      positiveLinear slope (wordMap ratio word 0) + ratio ^ word.length * positiveLinear slope tail := by
    rw [wordMap_affine]
    simp only [map_add, map_smul, smul_eq_mul]
  unfold linearWordReturn returnLevel
  apply (div_eq_iff (pow_ne_zero _ hpositive.ne')).mpr
  rw [hlevel] at hrestriction
  linarith

/-- A perfect affine fibre cannot touch an extreme of any cylinder hull.
The cylinder is relatively open, so such a touch would isolate its point. -/
theorem linearWordReturn_mem_Ioo_of_perfect {ratio slope level : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2) (hslope : 0 < slope)
    (perfectSubset : Set (ℝ × ℝ)) (hperfect : Perfect perfectSubset)
    (hsubset : perfectSubset ⊆
      {value | value ∈ cantorDust ratio ∧ positiveLinear slope value = level})
    {point : ℝ × ℝ} (hpoint : point ∈ perfectSubset)
    (word : List (Bool × Bool)) (hword : point ∈ wordCylinder ratio word) :
    linearWordReturn ratio (positiveLinear slope) word level ∈ Set.Ioo 0 (1 + slope) := by
  obtain ⟨other, hother_perfect, hother_word, hother_different⟩ :=
    perfect_cylinder_has_distinct hpositive hhalf perfectSubset hperfect
      (fun value membership => (hsubset membership).1) hpoint word hword
  obtain ⟨firstTail, hfirstTail, hfirst_eq⟩ := hword
  obtain ⟨secondTail, hsecondTail, hsecond_eq⟩ := hother_word
  have hdifferent : firstTail ≠ secondTail := by
    intro equality
    apply hother_different
    rw [← hsecond_eq, ← hfirst_eq, equality]
  have hfirst_level := linearWordReturn_of_preimage (slope := slope) (level := level) hpositive word firstTail
    (by rw [hfirst_eq]; exact (hsubset hpoint).2)
  have hsecond_level := linearWordReturn_of_preimage (slope := slope) (level := level) hpositive word secondTail
    (by rw [hsecond_eq]; exact (hsubset hother_perfect).2)
  exact positiveLinear_level_strict_of_two_points hpositive.le (by linarith) hslope
    hfirstTail hsecondTail hdifferent hfirst_level.symm hsecond_level.symm

end LambdaCantor.Last
