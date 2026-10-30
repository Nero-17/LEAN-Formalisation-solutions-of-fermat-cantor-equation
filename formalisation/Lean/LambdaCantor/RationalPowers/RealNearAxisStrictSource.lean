import LambdaCantor.RationalPowers.RealNearAxisRegularity

noncomputable section
namespace LambdaCantor.RationalPowers

/-- A strict real logarithmic source supplies one separated set of coordinate
bounds for every sufficiently small positive actual scale. -/
theorem real_near_axis_strict_bounds (exponent phase : ℝ) (horizontalDepth verticalDepth : ℕ)
    (horizontal vertical lowerBand upperBand : ℝ)
    (exponent_gt_one : 1 < exponent) (horizontal_positive : 0 < horizontal) (vertical_positive : 0 < vertical)
    (vertical_bound : vertical+1 ≤ (3 : ℝ)^verticalDepth)
    (band_lower : 1 < lowerBand) (band_upper : upperBand < 3) (upper_positive : 0 < upperBand)
    (lower_ratio : lowerBand/vertical < exponent/(horizontal+1))
    (upper_ratio : exponent/horizontal < upperBand/(vertical+1)) :
    ∃ verticalLower verticalUpper delta : ℝ,
      0 < verticalLower ∧ verticalUpper ≤ exponent/(horizontal+1) ∧
      exponent/horizontal ≤ 3*verticalLower ∧ 0 < delta ∧
      ∀ scale : ℝ, 0 < scale → scale < delta →
        ContinuousOn
          (fun point : ℝ × ℝ => realNearAxisLog exponent phase horizontalDepth verticalDepth
            horizontal vertical scale point.1 point.2)
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∧
        Classical.CoordinateBounds
          (realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical scale)
          (exponent/(horizontal+1)) (exponent/horizontal) verticalLower verticalUpper ∧
        (∀ y ∈ Set.Icc (0 : ℝ) 1,
          0 < realPowerDrop exponent scale ((vertical+1-y)/3^verticalDepth)) ∧
        ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
          0 < realNearAxisVertical exponent vertical scale y verticalDepth ∧
          lowerBand < (exponent/(horizontal+x))/realNearAxisVertical exponent vertical scale y verticalDepth ∧
          (exponent/(horizontal+x))/realNearAxisVertical exponent vertical scale y verticalDepth < upperBand := by
  have exponent_positive : 0 < exponent := by linarith
  have lower_positive : 0 < lowerBand := by linarith
  let verticalLower : ℝ := ((exponent/horizontal)/upperBand+1/(vertical+1))/2
  let verticalUpper : ℝ := (1/vertical+(exponent/(horizontal+1))/lowerBand)/2
  have lower_gap : (exponent/horizontal)/upperBand < 1/(vertical+1) := by
    apply (div_lt_iff₀ upper_positive).mpr
    simpa only [div_mul_eq_mul_div, one_mul] using upper_ratio
  have upper_gap : 1/vertical < (exponent/(horizontal+1))/lowerBand := by
    apply (lt_div_iff₀ lower_positive).mpr
    simpa only [div_mul_eq_mul_div, one_mul] using lower_ratio
  have lower_value_positive : 0 < verticalLower := by dsimp [verticalLower]; positivity
  have upper_value_positive : 0 < verticalUpper := by dsimp [verticalUpper]; positivity
  have lower_below : verticalLower < 1/(vertical+1) := by dsimp [verticalLower]; linarith
  have upper_above : 1/vertical < verticalUpper := by dsimp [verticalUpper]; linarith
  have lower_strong : exponent/horizontal < upperBand*verticalLower := by
    have base := (div_lt_iff₀ upper_positive).mp
      (show (exponent/horizontal)/upperBand < verticalLower by dsimp [verticalLower]; linarith)
    nlinarith
  have upper_strong : lowerBand*verticalUpper < exponent/(horizontal+1) := by
    have base := (lt_div_iff₀ lower_positive).mp
      (show verticalUpper < (exponent/(horizontal+1))/lowerBand by dsimp [verticalUpper]; linarith)
    nlinarith
  let error := min (1/(vertical+1)-verticalLower) (verticalUpper-1/vertical)/2
  have error_positive : 0 < error := by
    dsimp [error]
    exact div_pos (lt_min (sub_pos.mpr lower_below) (sub_pos.mpr upper_above)) (by norm_num)
  have error_lower : error < 1/(vertical+1)-verticalLower := by
    have bound := min_le_left (1/(vertical+1)-verticalLower) (verticalUpper-1/vertical)
    dsimp [error]
    linarith
  have error_upper : error < verticalUpper-1/vertical := by
    have bound := min_le_right (1/(vertical+1)-verticalLower) (verticalUpper-1/vertical)
    dsimp [error]
    linarith
  obtain ⟨delta, delta_positive, uniform⟩ := realNearAxisVertical_uniform exponent vertical verticalDepth
    exponent_positive vertical_positive vertical_bound error error_positive
  refine ⟨verticalLower, verticalUpper, delta, lower_value_positive, by nlinarith,
    by nlinarith, delta_positive, ?_⟩
  intro scale scale_positive scale_small
  have vertical_bounds : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      verticalLower ≤ realNearAxisVertical exponent vertical scale y verticalDepth ∧
      realNearAxisVertical exponent vertical scale y verticalDepth ≤ verticalUpper := by
    intro y y_bounds
    have denominator_positive : 0 < vertical+1-y := by linarith [y_bounds.2]
    have base_lower : 1/(vertical+1) ≤ 1/(vertical+1-y) :=
      div_le_div_of_nonneg_left (by norm_num) denominator_positive (by linarith [y_bounds.1])
    have base_upper : 1/(vertical+1-y) ≤ 1/vertical :=
      div_le_div_of_nonneg_left (by norm_num) vertical_positive (by linarith [y_bounds.2])
    have estimate := abs_lt.mp (uniform scale scale_positive scale_small y y_bounds).2
    constructor <;> linarith
  refine ⟨continuousOn_realNearAxisLog exponent_gt_one.le scale_positive.ne'
    horizontalDepth verticalDepth horizontal vertical horizontal_positive
    (fun y hy => (uniform scale scale_positive scale_small y hy).1), ?_,
    (fun y hy => (uniform scale scale_positive scale_small y hy).1), ?_⟩
  · apply Classical.coordinateBounds_of_hasDerivAt
      (realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical scale)
      (fun x _ => exponent/(horizontal+x))
      (fun _ y => realNearAxisVertical exponent vertical scale y verticalDepth)
    · intro x hx y hy
      exact realNearAxisLog_horizontal_derivative horizontalDepth verticalDepth horizontal vertical scale x y
        (by linarith [hx.1])
    · intro x hx y hy
      exact realNearAxisLog_vertical_derivative exponent_gt_one.le scale_positive.ne'
        horizontalDepth verticalDepth horizontal vertical x y (uniform scale scale_positive scale_small y hy).1
    · intro x hx y hy
      exact realNearAxisHorizontal_bounds exponent horizontal x exponent_positive horizontal_positive hx
    · intro x hx y hy
      exact vertical_bounds y hy
  · intro x hx y hy
    have horizontal_bounds := realNearAxisHorizontal_bounds exponent horizontal x exponent_positive horizontal_positive hx
    have vertical_bounds_at := vertical_bounds y hy
    have derivative_positive : 0 < realNearAxisVertical exponent vertical scale y verticalDepth :=
      lower_value_positive.trans_le vertical_bounds_at.1
    refine ⟨derivative_positive, (lt_div_iff₀ derivative_positive).mpr ?_,
      (div_lt_iff₀ derivative_positive).mpr ?_⟩
    · have multiplied := mul_le_mul_of_nonneg_left vertical_bounds_at.2 lower_positive.le
      nlinarith [horizontal_bounds.1]
    · have multiplied := mul_le_mul_of_nonneg_left vertical_bounds_at.1 upper_positive.le
      nlinarith [horizontal_bounds.2]

end LambdaCantor.RationalPowers

