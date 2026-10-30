import LambdaCantor.AE.CenteredResidual
import LambdaCantor.AE.CenteredWindowPower
import LambdaCantor.First.Transverse

noncomputable section
open Set Filter
open scoped Topology
namespace LambdaCantor.AE

/-- A uniform negative derivative quantitatively separates residual values. -/
theorem centered_residual_value_separation {residual : ℝ → ℝ} {lower upper slope : ℝ}
    (continuous : ContinuousOn residual (Icc lower upper))
    (differentiable : DifferentiableOn ℝ residual (Ioo lower upper))
    (derivative_bound : ∀ ratio ∈ Ioo lower upper, deriv residual ratio ≤ -slope)
    {first second : ℝ} (first_mem : first ∈ Icc lower upper) (second_mem : second ∈ Icc lower upper) :
    slope*|first-second| ≤ |residual first-residual second| := by
  have change := (convex_Icc lower upper).image_sub_le_mul_sub_of_deriv_le continuous
    (by simpa only [interior_Icc] using differentiable)
    (by simpa only [interior_Icc] using derivative_bound)
  rcases le_total first second with ordered | ordered
  · have bound := change first first_mem second second_mem ordered
    rw [abs_of_nonpos (sub_nonpos.mpr ordered)]
    have absolute := le_abs_self (residual first-residual second)
    nlinarith
  · have bound := change second second_mem first first_mem ordered
    rw [abs_of_nonneg (sub_nonneg.mpr ordered)]
    have absolute := neg_le_abs (residual first-residual second)
    nlinarith

/-- Quantitative comparison for zeros of the actual normalized centred residual.
Analytic derivative and tail-variation estimates are explicit inputs. -/
theorem centered_root_pair_displacement
    (exponent : ℝ) (horizontalDepth verticalDepth tailDepth : ℕ)
    (root : (ℕ → Bool × Bool) → ℝ) {lower upper slope error : ℝ}
    (slope_positive : 0 < slope)
    (root_mem : ∀ digits, root digits ∈ Icc lower upper)
    (root_zero : ∀ digits,
      centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits (root digits) = 0)
    (continuous : ∀ digits, ContinuousOn
      (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) (Icc lower upper))
    (differentiable : ∀ digits, DifferentiableOn ℝ
      (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) (Ioo lower upper))
    (derivative_bound : ∀ digits ratio, ratio ∈ Ioo lower upper →
      deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) ratio ≤ -slope)
    (first second : ℕ → Bool × Bool)
    (tail_bound : |centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth first (root second) -
      centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth second (root second)| ≤ error) :
    |root first-root second| ≤ error/slope := by
  have separated := centered_residual_value_separation (continuous first) (differentiable first)
    (derivative_bound first) (root_mem first) (root_mem second)
  rw [root_zero first, zero_sub, abs_neg] at separated
  rw [root_zero second, sub_zero] at tail_bound
  apply (le_div_iff₀ slope_positive).mpr
  exact (by simpa [mul_comm] using separated.trans tail_bound)

end LambdaCantor.AE
