import LambdaCantor.First.RootsAffineDensity

noncomputable section
open MeasureTheory
namespace LambdaCantor.First.Roots

/-- The L1 replacement error is unchanged when both densities are transported
from the common normalized root scale back to the original parameter line. -/
theorem affineDensity_difference_integral (center scale : ℝ) (scale_nonzero : scale ≠ 0)
    (first second : ℝ → ℝ) :
    (∫ point : ℝ, |affineDensity center scale first point - affineDensity center scale second point|) =
      ∫ point : ℝ, |first point - second point| := by
  simp only [affineDensity, ← mul_sub, abs_mul, abs_inv, abs_abs]
  rw [integral_const_mul]
  have translation : (∫ point : ℝ, |first ((point - center) / scale) - second ((point - center) / scale)|) =
      ∫ point : ℝ, |first (point / scale) - second (point / scale)| := by
    simpa only [sub_eq_add_neg] using
      integral_add_right_eq_self (fun point : ℝ => |first (point / scale) - second (point / scale)|) (-center)
  have dilation : (∫ point : ℝ, |first (point / scale) - second (point / scale)|) =
      |scale| * ∫ point : ℝ, |first point - second point| := by
    simpa only [smul_eq_mul] using
      (Measure.integral_comp_div (fun point : ℝ => |first point - second point|) scale)
  rw [translation, dilation]
  rw [← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr scale_nonzero), one_mul]

end LambdaCantor.First.Roots

