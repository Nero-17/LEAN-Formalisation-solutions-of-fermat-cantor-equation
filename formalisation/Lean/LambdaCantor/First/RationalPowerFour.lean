import LambdaCantor.First.Rational
import LambdaCantor.First.RationalCurvature

noncomputable section
namespace LambdaCantor.First

/-- The explicit smallness estimate for the quarter-endpoint curvature
factor in the powers-four construction. -/
theorem powers_four_curvature_smallness (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    (((4 ^ r - 2 : ℕ) : ℝ)) * (1 / 4 : ℝ) ^ (4 ^ r * k + r) ≤ 1 / 256 := by
  have hfour : 4 ≤ (4 : ℕ) ^ r := by
    simpa using (pow_le_pow_right₀ (by norm_num : 1 ≤ (4 : ℕ)) hr)
  have hdepth : 4 ^ r + r ≤ 4 ^ r * k + r := by
    have := Nat.mul_le_mul_left (4 ^ r) hk
    omega
  have hscale : (1 / 4 : ℝ) ^ (4 ^ r * k + r) ≤ (1 / 4 : ℝ) ^ (4 ^ r + r) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hdepth
  have hcoefficient : (((4 ^ r - 2 : ℕ) : ℝ)) ≤ (4 : ℝ) ^ r := by
    exact_mod_cast (Nat.sub_le (4 ^ r) 2)
  have hcancel : (4 : ℝ) ^ r * (1 / 4 : ℝ) ^ (4 ^ r + r) =
      (1 / 4 : ℝ) ^ (4 ^ r) := by
    rw [pow_add]
    calc
      (4 : ℝ) ^ r * ((1 / 4 : ℝ) ^ (4 ^ r) * (1 / 4 : ℝ) ^ r) =
          ((4 : ℝ) ^ r * (1 / 4 : ℝ) ^ r) * (1 / 4 : ℝ) ^ (4 ^ r) := by ring
      _ = _ := by rw [powers_four_cancellation]; ring
  calc
    (((4 ^ r - 2 : ℕ) : ℝ)) * (1 / 4 : ℝ) ^ (4 ^ r * k + r) ≤
        (4 : ℝ) ^ r * (1 / 4 : ℝ) ^ (4 ^ r * k + r) :=
      mul_le_mul_of_nonneg_right hcoefficient (by positivity)
    _ ≤ (4 : ℝ) ^ r * (1 / 4 : ℝ) ^ (4 ^ r + r) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = (1 / 4 : ℝ) ^ (4 ^ r) := hcancel
    _ ≤ (1 / 4 : ℝ) ^ 4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hfour
    _ = 1 / 256 := by norm_num

end LambdaCantor.First
