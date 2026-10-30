import LambdaCantor.Integer.SourceCoverage
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace LambdaCantor.Integer

open MeasureTheory

/-- The exact integral identity used in the infinite exponent tail. -/
theorem tail_log_integral (Z a b : ℝ) (ha : 0 < Z+a) (hb : 0 < Z+b) :
    (∫ s in a..b, Z/(Z+s)) = Z * Real.log ((Z+b)/(Z+a)) := by
  calc
    (∫ s in a..b, Z/(Z+s)) = Z * (∫ s in a..b, (Z+s)⁻¹) := by
      simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul]
    _ = Z * (∫ s in (Z+a)..(Z+b), s⁻¹) := by
      rw [intervalIntegral.integral_comp_add_left]
    _ = Z * Real.log ((Z+b)/(Z+a)) := by rw [integral_inv_of_pos ha hb]

theorem tail_integral_bounds_ordered (minimum Z a b : ℝ)
    (positive : 0 < minimum) (large : minimum ≤ Z)
    (nonnegative : 0 ≤ a) (ordered : a ≤ b) :
    (∫ s in a..b, minimum/(minimum+s)) ≤ (∫ s in a..b, Z/(Z+s)) ∧
    (∫ s in a..b, Z/(Z+s)) ≤ b-a := by
  have integrable (parameter : ℝ) (hp : 0 < parameter) :
      IntervalIntegrable (fun s => parameter/(parameter+s)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc ordered
    apply continuousOn_const.div (continuousOn_const.add continuousOn_id)
    intro s hs
    change parameter+s ≠ 0
    exact ne_of_gt (by linarith [hs.1])
  have positive_Z : 0 < Z := lt_of_lt_of_le positive large
  constructor
  · apply intervalIntegral.integral_mono_on ordered
      (integrable minimum positive) (integrable Z positive_Z)
    intro s hs
    exact (tail_integrand_bounds minimum Z s positive large (by linarith [hs.1])).1
  · have h := intervalIntegral.integral_mono_on ordered
      (integrable Z positive_Z) (continuous_const.intervalIntegrable a b)
      (fun s hs => (tail_integrand_bounds minimum Z s positive large
        (show 0 ≤ s by linarith [hs.1])).2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one] using h

/-- Both orientations of the integral are covered. This bounds every real
Z >= minimum; no finite sampling of exponents is substituted for the tail. -/
theorem tail_integral_enclosure (minimum Z a b : ℝ)
    (positive : 0 < minimum) (large : minimum ≤ Z)
    (nonnegative_a : 0 ≤ a) (nonnegative_b : 0 ≤ b) :
    min (∫ s in a..b, minimum/(minimum+s)) (b-a) ≤
      (∫ s in a..b, Z/(Z+s)) ∧
    (∫ s in a..b, Z/(Z+s)) ≤
      max (∫ s in a..b, minimum/(minimum+s)) (b-a) := by
  rcases le_total a b with hab | hba
  · obtain ⟨lower, upper⟩ := tail_integral_bounds_ordered minimum Z a b
      positive large nonnegative_a hab
    exact ⟨le_trans (min_le_left _ _) lower, le_trans upper (le_max_right _ _)⟩
  · obtain ⟨lower, upper⟩ := tail_integral_bounds_ordered minimum Z b a
      positive large nonnegative_b hba
    rw [intervalIntegral.integral_symm a b] at lower upper
    rw [intervalIntegral.integral_symm a b] at lower
    constructor
    · have hmin := min_le_right (∫ s in a..b, minimum/(minimum+s)) (b-a)
      linarith
    · have hmax := le_max_left (∫ s in a..b, minimum/(minimum+s)) (b-a)
      linarith

/-- The exact closed enclosure printed in the proof of integer-powers. -/
theorem tail_log_enclosure (minimum Z a b : ℝ)
    (positive : 0 < minimum) (large : minimum ≤ Z)
    (nonnegative_a : 0 ≤ a) (nonnegative_b : 0 ≤ b) :
    min (minimum * Real.log ((minimum+b)/(minimum+a))) (b-a) ≤
      Z * Real.log ((Z+b)/(Z+a)) ∧
    Z * Real.log ((Z+b)/(Z+a)) ≤
      max (minimum * Real.log ((minimum+b)/(minimum+a))) (b-a) := by
  have h := tail_integral_enclosure minimum Z a b positive large nonnegative_a nonnegative_b
  rw [tail_log_integral minimum a b (by linarith) (by linarith),
    tail_log_integral Z a b (by linarith) (by linarith)] at h
  exact h

end LambdaCantor.Integer
