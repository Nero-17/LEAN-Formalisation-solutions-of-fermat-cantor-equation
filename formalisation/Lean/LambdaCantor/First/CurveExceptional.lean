import LambdaCantor.First.CurveSlope
import LambdaCantor.First.LocalInverse
import LambdaCantor.First.Dimension

namespace LambdaCantor

open scoped NNReal

theorem contDiffOn_curveSlope {exponent : ℝ} (hexponent : 0 < exponent) :
    ContDiffOn ℝ 1 (curveSlope exponent) (Set.Ioo 0 1) := by
  have hfirst : ContDiffOn ℝ 1 (fun point : ℝ => point ^ (exponent - 1)) (Set.Ioo 0 1) :=
    contDiffOn_id.rpow_const_of_ne (fun point hpoint => hpoint.1.ne')
  have hpower : ContDiffOn ℝ 1 (fun point : ℝ => point ^ exponent) (Set.Ioo 0 1) :=
    contDiffOn_id.rpow_const_of_ne (fun point hpoint => hpoint.1.ne')
  have hsecond : ContDiffOn ℝ 1
      (fun point : ℝ => (1 - point ^ exponent) ^ (exponent⁻¹ - 1)) (Set.Ioo 0 1) := by
    apply (contDiffOn_const.sub hpower).rpow_const_of_ne
    intro point hpoint
    exact (sub_pos.mpr (Real.rpow_lt_one hpoint.1.le hpoint.2 hexponent)).ne'
  simpa only [curveSlope] using! hfirst.neg.mul hsecond

theorem curveSlope_locally_antilipschitz {exponent : ℝ} (hexponent : 1 < exponent) :
    ∀ point ∈ Set.Ioo (0 : ℝ) 1,
      ∃ (constant : ℝ≥0) (neighborhood : Set ℝ),
        neighborhood ∈ nhdsWithin point (Set.Ioo 0 1) ∧
        AntilipschitzWith constant (fun value : neighborhood => curveSlope exponent value) := by
  apply locally_antilipschitz_of_negative_derivative
    (contDiffOn_curveSlope (lt_trans zero_lt_one hexponent))
  intro point hpoint
  obtain ⟨derivative, hnegative, hderivative⟩ := curveSlope_hasDerivAt_negative hexponent hpoint
  rw [hderivative.deriv]
  exact hnegative

/-- Zero-dimensional exceptional tangent slopes contribute only a
zero-dimensional subset of the actual power arc. -/
theorem exceptional_power_arc_dimension_zero {exponent : ℝ} (hexponent : 1 < exponent)
    {exceptional : Set ℝ} (hzero : dimH exceptional = 0) :
    dimH (curvePoint exponent ''
      (Set.Ioo (0 : ℝ) 1 ∩ curveSlope exponent ⁻¹' exceptional)) = 0 :=
  First.exceptional_curve_dimension_zero (lt_trans zero_lt_one hexponent) hzero
    (curveSlope_locally_antilipschitz hexponent)

end LambdaCantor
