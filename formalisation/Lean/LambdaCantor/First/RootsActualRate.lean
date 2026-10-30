import LambdaCantor.First.RootsInterpolation

noncomputable section
namespace LambdaCantor.First.Roots

/-- The error in the actual coupled-density theorem is summable, including
its displacement constant inside the fractional interpolation power. -/
theorem summable_actual_replacement_rate (ratio exponent prefactor displacementConstant : ℝ)
    (ratio_nonnegative : 0 ≤ ratio) (ratio_lt_one : ratio < 1)
    (exponent_positive : 0 < exponent) (exponent_le_one : exponent ≤ 1)
    (displacement_nonnegative : 0 ≤ displacementConstant) :
    Summable (fun depth : ℕ => prefactor *
      (displacementConstant * ((depth : ℝ) + 1) * ratio ^ depth) ^ exponent) := by
  have base := (summable_replacement_rate ratio exponent ratio_nonnegative ratio_lt_one
    exponent_positive exponent_le_one).mul_left (prefactor * displacementConstant ^ exponent)
  apply base.congr
  intro depth
  have power_identity : (ratio ^ depth) ^ exponent = ratio ^ (exponent * (depth : ℝ)) := by
    rw [← Real.rpow_natCast ratio depth, ← Real.rpow_mul ratio_nonnegative]
    congr 1
    ring
  rw [Real.mul_rpow (mul_nonneg displacement_nonnegative (by positivity))
    (pow_nonneg ratio_nonnegative depth), Real.mul_rpow displacement_nonnegative (by positivity),
    power_identity]
  ring

end LambdaCantor.First.Roots
