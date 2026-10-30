import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Linarith

open scoped NNReal
namespace LambdaCantor

/-- A uniformly negative derivative gives a quantitative inverse Lipschitz
bound on a convex real domain. -/
theorem antilipschitz_of_derivative_le {domain : Set ℝ} {function : ℝ → ℝ}
    {slope : ℝ} (hslope : 0 < slope) (hconvex : Convex ℝ domain)
    (hcontinuous : ContinuousOn function domain)
    (hdifferentiable : DifferentiableOn ℝ function domain)
    (hderivative : ∀ point ∈ domain, deriv function point ≤ -slope) :
    AntilipschitzWith ⟨slope⁻¹, inv_nonneg.mpr hslope.le⟩
      (fun point : domain => function point) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro left right
  wlog hordered : (left : ℝ) ≤ right generalizing left right
  · simpa only [dist_comm] using this right left (le_of_not_ge hordered)
  have hbound := hconvex.image_sub_le_mul_sub_of_deriv_le hcontinuous
    (hdifferentiable.mono interior_subset)
    (fun point hpoint => hderivative point (interior_subset hpoint))
    left left.property right right.property hordered
  have hdecreasing : function right ≤ function left := by
    have h := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hslope.le) (sub_nonneg.mpr hordered)
    linarith
  change |(left : ℝ) - right| ≤ slope⁻¹ * |function left - function right|
  rw [abs_of_nonpos (sub_nonpos.mpr hordered), abs_of_nonneg (sub_nonneg.mpr hdecreasing)]
  have hquotient : (right : ℝ) - left ≤ (function left - function right) / slope := by
    apply (le_div_iff₀ hslope).mpr
    nlinarith
  simpa only [neg_sub, div_eq_mul_inv, mul_comm] using hquotient

/-- A C1 function with negative derivative has a locally Lipschitz inverse
on its open domain, in exactly the form needed for dimension transport. -/
theorem locally_antilipschitz_of_negative_derivative
    {function : ℝ → ℝ} (hsmooth : ContDiffOn ℝ 1 function (Set.Ioo 0 1))
    (hnegative : ∀ point ∈ Set.Ioo (0 : ℝ) 1, deriv function point < 0) :
    ∀ point ∈ Set.Ioo (0 : ℝ) 1,
      ∃ (constant : ℝ≥0) (neighborhood : Set ℝ),
        neighborhood ∈ nhdsWithin point (Set.Ioo 0 1) ∧
        AntilipschitzWith constant (fun value : neighborhood => function value) := by
  intro point hpoint
  have hcontinuous := hsmooth.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hat : ContinuousAt (deriv function) point :=
    (hcontinuous point hpoint).continuousAt (isOpen_Ioo.mem_nhds hpoint)
  have hnear : {value | value ∈ Set.Ioo (0 : ℝ) 1 ∧
      deriv function value < deriv function point / 2} ∈ nhds point :=
    Filter.inter_mem (isOpen_Ioo.mem_nhds hpoint)
      (hat.eventually (gt_mem_nhds (by linarith [hnegative point hpoint])))
  obtain ⟨radius, hradius, hsubset⟩ := Metric.mem_nhds_iff.mp hnear
  have hslope : 0 < -(deriv function point / 2) := by linarith [hnegative point hpoint]
  refine ⟨⟨(-(deriv function point / 2))⁻¹, inv_nonneg.mpr hslope.le⟩,
    Metric.ball point radius, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hradius), ?_⟩
  apply antilipschitz_of_derivative_le hslope (convex_ball point radius)
  · exact hsmooth.continuousOn.mono (fun value hvalue => (hsubset hvalue).1)
  · exact (hsmooth.differentiableOn (by norm_num)).mono (fun value hvalue => (hsubset hvalue).1)
  · intro value hvalue
    have h := (hsubset hvalue).2
    linarith

end LambdaCantor
