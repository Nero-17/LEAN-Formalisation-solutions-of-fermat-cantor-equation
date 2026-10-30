import LambdaCantor.Circle.OnsetAlgebra

namespace LambdaCantor.Circle

/-- Algebraic identity in the positive-measure construction, with `scale`
standing for the genuine cylinder scale `ratio ^ k`. No equation is assumed. -/
theorem root_residual_identity (ratio scale firstTail secondTail : ℝ) :
    ((1 - ratio) * scale + ratio * scale ^ 3 * firstTail) ^ 2 +
      (1 - ratio * scale ^ 2 + ratio * scale ^ 4 * secondTail) ^ 2 - 1 =
    scale ^ 2 * (-(4 * ratio - 1 - ratio ^ 2) +
      2 * ratio * scale ^ 2 * ((1 - ratio) * firstTail + secondTail) +
      ratio ^ 2 * scale ^ 4 * firstTail ^ 2 +
      ratio ^ 2 * scale ^ 2 * (1 - scale ^ 2 * secondTail) ^ 2) := by ring

theorem upper_endpoint_margin :
    (35 / 1000 : ℚ) < 4 * (7 / 25) - 1 - (7 / 25) ^ 2 -
      2 * (7 / 25) ^ 5 * (2 - 7 / 25) - (7 / 25) ^ 10 - (7 / 25) ^ 6 := by
  norm_num

theorem derivative_error_margin :
    2 * (10 * (7 / 25 : ℚ) ^ 4 + 7 * (7 / 25) ^ 5) +
      10 * (7 / 25) ^ 9 + 6 * (7 / 25) ^ 10 + 6 * (7 / 25) ^ 5 +
      2 * (7 / 25) ^ 6 * (4 * (7 / 25) ^ 3 + 3 * (7 / 25) ^ 4) < 158 / 1000 := by
  norm_num

theorem onset_residual_positive (scale firstTail secondTail : ℝ)
    (scale_positive : 0 < scale) (scale_lt_one : scale < 1)
    (first_nonnegative : 0 ≤ firstTail)
    (second_nonnegative : 0 ≤ secondTail) (second_bounded : secondTail ≤ 1) :
    0 < -(4 * onset - 1 - onset ^ 2) +
      2 * onset * scale ^ 2 * ((1 - onset) * firstTail + secondTail) +
      onset ^ 2 * scale ^ 4 * firstTail ^ 2 +
      onset ^ 2 * scale ^ 2 * (1 - scale ^ 2 * secondTail) ^ 2 := by
  have threshold := onset_equation
  have onset_positive := onset_pos
  have onset_small := onset_lt_one_third
  have onset_complement : 0 ≤ 1 - onset := by linarith
  have scale_squared : scale ^ 2 < 1 := by nlinarith
  have inner_positive : 0 < 1 - scale ^ 2 * secondTail := by
    have : scale ^ 2 * secondTail ≤ scale ^ 2 := by nlinarith [sq_nonneg scale]
    linarith
  have strict_term : 0 < onset ^ 2 * scale ^ 2 * (1 - scale ^ 2 * secondTail) ^ 2 := by positivity
  have first_term : 0 ≤ 2 * onset * scale ^ 2 * ((1 - onset) * firstTail + secondTail) := by positivity
  have second_term : 0 ≤ onset ^ 2 * scale ^ 4 * firstTail ^ 2 := by positivity
  nlinarith

end LambdaCantor.Circle
