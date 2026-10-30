import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

namespace LambdaCantor.Circle

/-- The exact candidate threshold in Theorem 5.2. -/
noncomputable def onset : ℝ := 2 - Real.sqrt 3

theorem onset_pos : 0 < onset := by
  have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have := Real.sqrt_nonneg (3 : ℝ)
  dsimp [onset]
  nlinarith

theorem onset_lt_one_third : onset < (1 / 3 : ℝ) := by
  have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have := Real.sqrt_nonneg (3 : ℝ)
  dsimp [onset]
  nlinarith

theorem onset_lt_twenty_seven_hundredths : onset < (27 / 100 : ℝ) := by
  have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have := Real.sqrt_nonneg (3 : ℝ)
  dsimp [onset]
  nlinarith

theorem onset_equation : (1 - onset) ^ 2 = 2 * onset := by
  have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  dsimp [onset]
  nlinarith

theorem below_onset_quadratic (ratio : ℝ) (nonneg : 0 ≤ ratio)
    (below : ratio ≤ onset) : 2 * ratio ≤ (1 - ratio) ^ 2 := by
  have := onset_equation
  have := onset_lt_one_third
  nlinarith [sq_nonneg (onset - ratio)]

/-- This is the scalar contradiction for `m - 2k ≤ 0` in the onset proof.
The hypotheses are the bounds supplied by the outer Cantor cylinder. -/
theorem nonpositive_scale_exclusion (ratio outerX outerY scale deficit : ℝ)
    (ratio_nonneg : 0 ≤ ratio) (ratio_le : ratio ≤ onset)
    (x_nonneg : 0 ≤ outerX) (x_le : outerX ≤ 1)
    (y_lower : 1 - ratio ≤ outerY)
    (scale_lower : 1 ≤ scale) (deficit_le : deficit ≤ ratio) :
    outerX ^ 2 ≠ scale * outerY * (2 - deficit) := by
  have ratio_small : ratio < (1 / 3 : ℝ) := lt_of_le_of_lt ratio_le onset_lt_one_third
  have y_positive : 0 < outerY := by linarith
  have deficit_positive : 0 < 2 - deficit := by linarith
  have product_lower : (1 - ratio) * (2 - ratio) ≤ scale * outerY * (2 - deficit) := by
    calc
      (1 - ratio) * (2 - ratio) ≤ outerY * (2 - deficit) := by gcongr <;> linarith
      _ ≤ scale * outerY * (2 - deficit) := by nlinarith [mul_pos y_positive deficit_positive]
  have : 1 < (1 - ratio) * (2 - ratio) := by nlinarith [sq_nonneg ratio]
  nlinarith [mul_nonneg x_nonneg (sub_nonneg.mpr x_le)]

/-- The scalar contradiction for `m - 2k ≥ 1`. Positivity of the deficit
gives the strict inequality needed also at the threshold itself. -/
theorem positive_scale_exclusion (ratio outerX outerY scale deficit : ℝ)
    (ratio_pos : 0 < ratio) (ratio_le : ratio ≤ onset)
    (x_lower : 1 - ratio ≤ outerX)
    (y_nonneg : 0 ≤ outerY) (y_le : outerY ≤ 1)
    (scale_nonneg : 0 ≤ scale) (scale_le : scale ≤ ratio)
    (deficit_pos : 0 < deficit) (deficit_le : deficit ≤ 1) :
    outerX ^ 2 ≠ scale * outerY * (2 - deficit) := by
  have ratio_small : ratio < (1 / 3 : ℝ) := lt_of_le_of_lt ratio_le onset_lt_one_third
  have x_nonneg : 0 ≤ outerX := by linarith
  have product_upper : scale * outerY * (2 - deficit) ≤ ratio * (2 - deficit) := by
    calc
      scale * outerY * (2 - deficit) ≤ ratio * 1 * (2 - deficit) := by gcongr <;> linarith
      _ = ratio * (2 - deficit) := by ring
  have threshold := below_onset_quadratic ratio (le_of_lt ratio_pos) ratio_le
  have square_lower : (1 - ratio) ^ 2 ≤ outerX ^ 2 := by nlinarith
  have : ratio * (2 - deficit) < 2 * ratio := by nlinarith [mul_pos ratio_pos deficit_pos]
  linarith

end LambdaCantor.Circle
