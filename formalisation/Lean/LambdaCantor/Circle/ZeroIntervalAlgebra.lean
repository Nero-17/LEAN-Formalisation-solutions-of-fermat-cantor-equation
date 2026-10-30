import LambdaCantor.Circle.ProjectionGap

namespace LambdaCantor.Circle

/-- Exact polynomial normalization after the two forced cylinders. -/
theorem forced_cylinder_residual (ratio tailScale relativeScale firstTail secondTail level : ℝ)
    (level_equation : ratio ^ 2 * tailScale * level = 4 * ratio - 1 - ratio ^ 2) :
    (1 - ratio + ratio * tailScale * firstTail) ^ 2 -
      2 * ratio * (1 - tailScale * secondTail) +
      ratio ^ 2 * tailScale * relativeScale * (1 - tailScale * secondTail) ^ 2 =
    ratio * tailScale * (2 * ((1 - ratio) * firstTail + secondTail) +
      ratio * tailScale * firstTail ^ 2 +
      ratio * relativeScale * (1 - tailScale * secondTail) ^ 2 - ratio * level) := by
  nlinarith [level_equation]

/-- The error interval used in both projection-gap exclusions. The natural
depth assumptions enter only through `tailScale ≤ ratio^6` and `relativeScale ≤ 1`. -/
theorem forced_cylinder_projection_enclosure
    (ratio tailScale relativeScale firstTail secondTail level : ℝ)
    (ratio_positive : 0 < ratio) (ratio_le_one : ratio ≤ 1)
    (tail_nonnegative : 0 ≤ tailScale) (tail_bound : tailScale ≤ ratio ^ 6)
    (relative_nonnegative : 0 ≤ relativeScale) (relative_bound : relativeScale ≤ 1)
    (first_nonnegative : 0 ≤ firstTail) (first_bound : firstTail ≤ 1)
    (second_nonnegative : 0 ≤ secondTail) (second_bound : secondTail ≤ 1)
    (normalized_equation : ratio * level = 2 * ((1 - ratio) * firstTail + secondTail) +
      ratio * tailScale * firstTail ^ 2 +
      ratio * relativeScale * (1 - tailScale * secondTail) ^ 2) :
    ratio / 2 * (level - relativeScale) - ratio ^ 7 / 2 ≤
        (1 - ratio) * firstTail + secondTail ∧
      (1 - ratio) * firstTail + secondTail ≤
        ratio / 2 * (level - relativeScale) + ratio ^ 7 := by
  have sixth_bound : ratio ^ 6 ≤ 1 := pow_le_one₀ ratio_positive.le ratio_le_one
  have tail_le_one : tailScale ≤ 1 := le_trans tail_bound sixth_bound
  have first_square_bound : firstTail ^ 2 ≤ 1 := by nlinarith
  have product_nonnegative : 0 ≤ tailScale * secondTail := mul_nonneg tail_nonnegative second_nonnegative
  have product_bound : tailScale * secondTail ≤ 1 := by
    calc
      _ ≤ tailScale * 1 := mul_le_mul_of_nonneg_left second_bound tail_nonnegative
      _ ≤ 1 := by simpa using tail_le_one
  have square_correction_nonnegative : 0 ≤ 2 * tailScale * secondTail - (tailScale * secondTail) ^ 2 := by
    nlinarith [mul_nonneg product_nonnegative (sub_nonneg.mpr product_bound)]
  have square_correction_bound : 2 * tailScale * secondTail - (tailScale * secondTail) ^ 2 ≤ 2 * tailScale := by
    nlinarith [mul_nonneg tail_nonnegative (sub_nonneg.mpr second_bound), sq_nonneg (tailScale * secondTail)]
  have negative_error_nonnegative : 0 ≤ ratio * tailScale * firstTail ^ 2 := by positivity
  have negative_error_bound : ratio * tailScale * firstTail ^ 2 ≤ ratio ^ 7 := by
    calc
      _ ≤ ratio * tailScale * 1 := mul_le_mul_of_nonneg_left first_square_bound (mul_nonneg ratio_positive.le tail_nonnegative)
      _ ≤ ratio * ratio ^ 6 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left tail_bound ratio_positive.le
      _ = ratio ^ 7 := by ring
  have positive_error_nonnegative : 0 ≤ ratio * relativeScale *
      (2 * tailScale * secondTail - (tailScale * secondTail) ^ 2) := by positivity
  have positive_error_bound : ratio * relativeScale *
      (2 * tailScale * secondTail - (tailScale * secondTail) ^ 2) ≤ 2 * ratio ^ 7 := by
    calc
      _ ≤ ratio * 1 * (2 * tailScale) := by gcongr
      _ ≤ ratio * 1 * (2 * ratio ^ 6) := by gcongr
      _ = 2 * ratio ^ 7 := by ring
  constructor <;> nlinarith [normalized_equation]

/-- This combines the two actual Cantor projection gaps. The remaining
zero-interval theorem must prove the displayed cylinder and depth hypotheses;
they are not treated as a completed main theorem. -/
theorem forced_cylinders_exclude_solution
    (ratio tailScale relativeScale firstTail secondTail level : ℝ)
    (lower : (2679 / 10000 : ℝ) ≤ ratio) (upper : ratio ≤ (67 / 250 : ℝ))
    (tail_nonnegative : 0 ≤ tailScale) (tail_bound : tailScale ≤ ratio ^ 6)
    (relative_nonnegative : 0 ≤ relativeScale)
    (relative_alternative : relativeScale = 1 ∨ relativeScale ≤ ratio ^ 2)
    (first_mem : firstTail ∈ cantorSet ratio) (second_mem : secondTail ∈ cantorSet ratio)
    (level_lower : (379 / 100 : ℝ) < level) (level_upper : level < (381 / 100 : ℝ))
    (normalized_equation : ratio * level = 2 * ((1 - ratio) * firstTail + secondTail) +
      ratio * tailScale * firstTail ^ 2 +
      ratio * relativeScale * (1 - tailScale * secondTail) ^ 2) : False := by
  have positive : 0 < ratio := by linarith
  have less_one : ratio < 1 := by linarith
  have first_bounds := cantorSet_subset_unitInterval positive.le less_one first_mem
  have second_bounds := cantorSet_subset_unitInterval positive.le less_one second_mem
  have relative_bound : relativeScale ≤ 1 := by
    rcases relative_alternative with equality | bounded
    · linarith
    · have : ratio ^ 2 ≤ 1 := pow_le_one₀ positive.le less_one.le
      linarith
  have enclosure := forced_cylinder_projection_enclosure ratio tailScale relativeScale firstTail secondTail level
    positive less_one.le tail_nonnegative tail_bound relative_nonnegative relative_bound
    first_bounds.1 first_bounds.2 second_bounds.1 second_bounds.2 normalized_equation
  rcases relative_alternative with equality | bounded
  · rw [equality] at enclosure
    exact first_scale_projection_exclusion lower upper first_mem second_mem level_lower level_upper
      enclosure.1 enclosure.2
  · exact later_scale_projection_exclusion lower upper first_mem second_mem level_lower level_upper
      relative_nonnegative bounded enclosure.1 enclosure.2

end LambdaCantor.Circle
