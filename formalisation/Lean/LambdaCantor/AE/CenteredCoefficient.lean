import LambdaCantor.AE.CenteredResidualLimit
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
namespace LambdaCantor.AE

theorem centered_exp_sub_one_bound {value : ℝ} (hvalue : |value| ≤ 1) :
    |Real.exp value - 1| ≤ Real.exp 1 * |value| := by
  have hestimate := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun point _ => (Real.hasDerivAt_exp point).differentiableAt)
    (fun point hpoint => by
      rw [(Real.hasDerivAt_exp point).deriv, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos point)]
      exact Real.exp_le_exp.mpr hpoint.2)
    (show (0 : ℝ) ∈ Set.Icc (-1) 1 by norm_num) (abs_le.mp hvalue)
  simpa only [Real.exp_zero, Real.norm_eq_abs, sub_zero] using hestimate

theorem centered_coefficient_near_one {exponent center discrepancy epsilon : ℝ}
    (hexponent : 0 < exponent) (hcenter : 0 < center) (hless : center < 1)
    (hphase : |discrepancy + Real.log exponent / Real.log center| ≤ epsilon)
    (hsmall : |Real.log center| * epsilon ≤ 1) :
    |exponent * center ^ discrepancy - 1| ≤ Real.exp 1 * |Real.log center| * epsilon := by
  have hidentity : exponent * center ^ discrepancy =
      Real.exp (Real.log center * (discrepancy + Real.log exponent / Real.log center)) := by
    calc
      _ = (exponent * center ^ (-Real.log exponent / Real.log center)) *
          center ^ (discrepancy + Real.log exponent / Real.log center) := by
        rw [mul_assoc, ← Real.rpow_add hcenter]
        congr 2
        ring
      _ = _ := by
        rw [centered_resonance_at_center hexponent hcenter hless, one_mul,
          Real.rpow_def_of_pos hcenter]
  have hproduct : |Real.log center * (discrepancy + Real.log exponent / Real.log center)| ≤
      |Real.log center| * epsilon := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hphase (abs_nonneg _)
  rw [hidentity]
  exact (centered_exp_sub_one_bound (hproduct.trans hsmall)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hproduct (Real.exp_pos 1).le)

end LambdaCantor.AE
