import LambdaCantor.Last.AnalyticIsolatedApproximateOrbit

noncomputable section
namespace LambdaCantor.Last

/-- Actual small-phase mixed children are covered by the other three hulls,
even when the two mixed hulls exchange order under a C¹ perturbation. This is
the strict outer-cover comparison needed at tangent ratio exactly one. -/
theorem small_phase_actual_child_not_mixed {ratio slope level error : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2) (slope_lower : 1 ≤ slope)
    (outer_room : 2*error < 1-ratio)
    (mixed_room : 2*error < ratio-(1-2*ratio)*slope)
    (lower upper : Bool × Bool → ℝ) (digit : Bool × Bool)
    (inside : level ∈ Set.Icc (lower digit) (upper digit))
    (unique : ∀ other : Bool × Bool, other ≠ digit → level ∉ Set.Icc (lower other) (upper other))
    (lower_error : ∀ child, |lower child-affineChildOffset ratio slope child| ≤ error)
    (upper_error : ∀ child, |upper child-(affineChildOffset ratio slope child+ratio*(1+slope))| ≤ error) :
    digit = (false,false) ∨ digit = (true,true) := by
  have lower00 := abs_le.mp (lower_error (false,false))
  have lower10 := abs_le.mp (lower_error (true,false))
  have lower01 := abs_le.mp (lower_error (false,true))
  have lower11 := abs_le.mp (lower_error (true,true))
  have upper00 := abs_le.mp (upper_error (false,false))
  have upper10 := abs_le.mp (upper_error (true,false))
  have upper01 := abs_le.mp (upper_error (false,true))
  have upper11 := abs_le.mp (upper_error (true,true))
  simp only [affineChildOffset, Bool.false_eq_true, if_false, if_true, mul_zero,
    zero_add, add_zero, mul_one] at lower00 lower10 lower01 lower11 upper00 upper10 upper01 upper11
  have reference_order : 0 ≤ (slope-1)*(1-ratio) :=
    mul_nonneg (sub_nonneg.mpr slope_lower) (by linarith)
  rcases digit with ⟨first, second⟩
  cases first <;> cases second
  · exact Or.inl rfl
  · exfalso
    by_cases below : level < lower (true,false)
    · apply unique (false,false) (by decide)
      constructor <;> nlinarith [inside.1, inside.2]
    · have above : upper (true,false) < level := by
        by_contra not_above
        exact unique (true,false) (by decide) ⟨le_of_not_gt below, le_of_not_gt not_above⟩
      apply unique (true,true) (by decide)
      constructor <;> nlinarith [inside.1, inside.2]
  · exfalso
    by_cases below : level < lower (false,true)
    · apply unique (false,false) (by decide)
      constructor <;> nlinarith [inside.1, inside.2]
    · have above : upper (false,true) < level := by
        by_contra not_above
        exact unique (false,true) (by decide) ⟨le_of_not_gt below, le_of_not_gt not_above⟩
      apply unique (true,true) (by decide)
      constructor <;> nlinarith [inside.1, inside.2]
  · exact Or.inr rfl

theorem small_phase_actual_hull_approx_exclusive {ratio slope actualLevel tangentLevel error : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2) (slope_lower : 1 ≤ slope)
    (outer_room : 2*error < 1-ratio)
    (mixed_room : 2*error < ratio-(1-2*ratio)*slope)
    (lower upper : Bool × Bool → ℝ) (digit : Bool × Bool)
    (inside : actualLevel ∈ Set.Icc (lower digit) (upper digit))
    (unique : ∀ other : Bool × Bool, other ≠ digit → actualLevel ∉ Set.Icc (lower other) (upper other))
    (lower_error : ∀ child, |lower child-affineChildOffset ratio slope child| ≤ error)
    (upper_error : ∀ child, |upper child-(affineChildOffset ratio slope child+ratio*(1+slope))| ≤ error)
    (level_error : |tangentLevel-actualLevel| ≤ error) :
    ApproxAffineExclusiveRegion ratio slope tangentLevel (2*error) digit := by
  have symbols := small_phase_actual_child_not_mixed positive less_half slope_lower outer_room mixed_room
    lower upper digit inside unique lower_error upper_error
  have level_bounds := abs_le.mp level_error
  rcases symbols with digit_zero | digit_one
  · subst digit
    have lower10 := abs_le.mp (lower_error (true,false))
    have upper00 := abs_le.mp (upper_error (false,false))
    have upper10 := abs_le.mp (upper_error (true,false))
    simp only [affineChildOffset, Bool.false_eq_true, if_false, if_true,
      mul_zero, zero_add, add_zero, mul_one] at lower10 upper00 upper10
    change tangentLevel ≤ 1-ratio+2*error
    have exclusive : actualLevel ≤ lower (true,false) := by
      by_contra failure
      apply unique (true,false) (by decide)
      constructor
      · exact (lt_of_not_ge failure).le
      · nlinarith [inside.2]
    linarith
  · subst digit
    have upper01 := abs_le.mp (upper_error (false,true))
    have lower01 := abs_le.mp (lower_error (false,true))
    have lower11 := abs_le.mp (lower_error (true,true))
    simp only [affineChildOffset, Bool.false_eq_true, if_false, if_true,
      mul_zero, zero_add, add_zero, mul_one] at upper01 lower01 lower11
    change ratio+slope-2*error ≤ tangentLevel
    have exclusive : upper (false,true) ≤ actualLevel := by
      by_contra failure
      apply unique (false,true) (by decide)
      constructor
      · nlinarith [inside.1]
      · exact (lt_of_not_ge failure).le
    nlinarith

end LambdaCantor.Last
