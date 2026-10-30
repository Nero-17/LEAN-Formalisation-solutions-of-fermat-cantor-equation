import LambdaCantor.First.Transverse
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
namespace LambdaCantor.AE

/-- A center residual of order scale and a uniformly negative derivative
give opposite endpoint signs on a sufficiently wide centered window. -/
theorem centered_root_window_signs {residual : ℝ → ℝ}
    {center scale width slope errorBound : ℝ}
    (hscale : 0 < scale) (hwidth : 0 < width) (hslope : 0 < slope)
    (hwidthSlope : errorBound < slope * width)
    (hcontinuous : ContinuousOn residual (Set.Icc (center - width * scale) (center + width * scale)))
    (hdifferentiable : DifferentiableOn ℝ residual (Set.Ioo (center - width * scale) (center + width * scale)))
    (hderivative : ∀ parameter ∈ Set.Ioo (center - width * scale) (center + width * scale),
      deriv residual parameter ≤ -slope)
    (hcenter : |residual center| ≤ errorBound * scale) :
    0 < residual (center - width * scale) ∧ residual (center + width * scale) < 0 := by
  have hwidthScale : 0 < width * scale := mul_pos hwidth hscale
  have hinterval : center - width * scale ≤ center + width * scale := by linarith
  have hcenterMem : center ∈ Set.Icc (center - width * scale) (center + width * scale) := by
    constructor <;> linarith
  have hleft := (convex_Icc (center - width * scale) (center + width * scale)).image_sub_le_mul_sub_of_deriv_le
    hcontinuous (by simpa only [interior_Icc] using hdifferentiable)
    (by simpa only [interior_Icc] using hderivative)
    (center - width * scale) ⟨le_rfl, hinterval⟩ center hcenterMem hcenterMem.1
  have hright := (convex_Icc (center - width * scale) (center + width * scale)).image_sub_le_mul_sub_of_deriv_le
    hcontinuous (by simpa only [interior_Icc] using hdifferentiable)
    (by simpa only [interior_Icc] using hderivative)
    center hcenterMem (center + width * scale) ⟨hinterval, le_rfl⟩ hcenterMem.2
  have hcenterBounds := abs_le.mp hcenter
  have hgap := mul_pos (sub_pos.mpr hwidthSlope) hscale
  constructor <;> nlinarith

theorem centered_root_window_exists_unique {residual : ℝ → ℝ}
    {center scale width slope errorBound : ℝ}
    (hscale : 0 < scale) (hwidth : 0 < width) (hslope : 0 < slope)
    (hwidthSlope : errorBound < slope * width)
    (hcontinuous : ContinuousOn residual (Set.Icc (center - width * scale) (center + width * scale)))
    (hdifferentiable : DifferentiableOn ℝ residual (Set.Ioo (center - width * scale) (center + width * scale)))
    (hderivative : ∀ parameter ∈ Set.Ioo (center - width * scale) (center + width * scale),
      deriv residual parameter ≤ -slope)
    (hcenter : |residual center| ≤ errorBound * scale) :
    ∃! root : ℝ, root ∈ Set.Icc (center - width * scale) (center + width * scale) ∧ residual root = 0 := by
  have hsigns := centered_root_window_signs hscale hwidth hslope hwidthSlope
    hcontinuous hdifferentiable hderivative hcenter
  have hinterval : center - width * scale ≤ center + width * scale := by
    have := mul_pos hwidth hscale
    linarith
  obtain ⟨root, hroot, hzero⟩ := intermediate_value_Icc' hinterval hcontinuous
    (show (0 : ℝ) ∈ Set.Icc (residual (center + width * scale)) (residual (center - width * scale)) from
      ⟨hsigns.2.le, hsigns.1.le⟩)
  have hanti := strictAntiOn_of_uniform_negative_derivative hcontinuous hslope hderivative
  refine ⟨root, ⟨hroot, hzero⟩, ?_⟩
  intro other hother
  exact hanti.injOn hother.1 hroot (hother.2.trans hzero.symm)

end LambdaCantor.AE
