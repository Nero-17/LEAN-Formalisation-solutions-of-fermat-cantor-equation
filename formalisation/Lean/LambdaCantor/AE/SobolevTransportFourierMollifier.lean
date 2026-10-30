import LambdaCantor.AE.SobolevTransportMollifier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
open MeasureTheory Filter
open scoped FourierTransform

namespace LambdaCantor.AE

theorem norm_fourierChar_sub_one_le_linear (value : ℝ) :
    ‖(Real.fourierChar value : ℂ) - 1‖ ≤ 2 * Real.pi * |value| := by
  have hbound := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * value)
  simpa [Real.fourierChar_apply, mul_comm, Complex.ofReal_mul, Real.norm_eq_abs,
    abs_mul, abs_of_pos Real.pi_pos] using hbound

theorem norm_fourierChar_sub_one_le_holder {regularity : ℝ}
    (hregularity : 0 ≤ regularity) (hregularityOne : regularity ≤ 1) (value : ℝ) :
    ‖(Real.fourierChar value : ℂ) - 1‖ ≤
      (2 * Real.pi + 2) * |value| ^ regularity := by
  by_cases hsmall : |value| ≤ 1
  · have hpower := Real.self_le_rpow_of_le_one (abs_nonneg value) hsmall hregularityOne
    have hlinear := norm_fourierChar_sub_one_le_linear value
    have hproduct := mul_le_mul_of_nonneg_left hpower (by positivity : 0 ≤ 2 * Real.pi)
    nlinarith [Real.rpow_nonneg (abs_nonneg value) regularity]
  · have hpower := Real.one_le_rpow (lt_of_not_ge hsmall).le hregularity
    have htwo : ‖(Real.fourierChar value : ℂ) - 1‖ ≤ 2 := by
      simpa only [Circle.norm_coe, norm_one, one_add_one_eq_two] using
        norm_sub_le (Real.fourierChar value : ℂ) 1
    nlinarith [Real.pi_pos]

theorem transportMollifier_fourier_error_bound {scale regularity : ℝ}
    (hscale : 0 < scale) (hregularity : 0 ≤ regularity)
    (hregularityOne : regularity ≤ 1) (frequency : ℝ) :
    ‖𝓕 (fun value => (transportMollifier scale value : ℂ)) frequency - 1‖ ≤
      (2 * Real.pi + 2) * scale ^ regularity * |frequency| ^ regularity := by
  have hreal := integrable_transportMollifier hscale
  have hcomplex : Integrable (fun value => (transportMollifier scale value : ℂ)) :=
    hreal.mono ((Complex.continuous_ofReal.comp
      (contDiff_transportMollifier scale).continuous).aestronglyMeasurable)
      (Eventually.of_forall (fun value => by simp))
  have hintegrand : Integrable (fun value : ℝ =>
      (Real.fourierChar (-(value * frequency)) : ℂ) * transportMollifier scale value) := by
    apply hcomplex.mono
      (((show Continuous (fun value : ℝ =>
        (Real.fourierChar (-(value * frequency)) : ℂ)) from by
          simp_rw [Real.fourierChar_apply]
          fun_prop).mul
          (Complex.continuous_ofReal.comp (contDiff_transportMollifier scale).continuous)).aestronglyMeasurable)
    refine Eventually.of_forall (fun value => le_of_eq ?_)
    exact (norm_mul (Real.fourierChar (-(value * frequency)) : ℂ)
      (transportMollifier scale value : ℂ)).trans
        ((congrArg (fun factor : ℝ => factor * ‖(transportMollifier scale value : ℂ)‖)
          (Circle.norm_coe (Real.fourierChar (-(value * frequency))))).trans (one_mul _))
  have hidentity :
      𝓕 (fun value => (transportMollifier scale value : ℂ)) frequency - 1 =
      ∫ value : ℝ, ((Real.fourierChar (-(value * frequency)) : ℂ) - 1) *
        transportMollifier scale value := by
    rw [Real.fourier_real_eq]
    simp only [Circle.smul_def, smul_eq_mul]
    conv_lhs =>
      rw [show (1 : ℂ) = ∫ value : ℝ, (transportMollifier scale value : ℂ) from by
        rw [integral_complex_ofReal, integral_transportMollifier hscale]; rfl]
    rw [← integral_sub hintegrand hcomplex]
    congr 1
    funext value
    ring
  have hpointwise (value : ℝ) :
      ‖((Real.fourierChar (-(value * frequency)) : ℂ) - 1) * transportMollifier scale value‖ ≤
      ((2 * Real.pi + 2) * scale ^ regularity * |frequency| ^ regularity) *
        transportMollifier scale value := by
    by_cases hzero : transportMollifier scale value = 0
    · simp only [hzero, Complex.ofReal_zero, mul_zero, norm_zero, le_refl]
    · have hsupport := tsupport_transportMollifier_subset hscale
        (subset_tsupport _ (show value ∈ Function.support (transportMollifier scale) from hzero))
      have habsolute := (abs_lt.mpr hsupport).le
      have hchar := norm_fourierChar_sub_one_le_holder hregularity hregularityOne (-(value * frequency))
      rw [abs_neg, abs_mul, Real.mul_rpow (abs_nonneg value) (abs_nonneg frequency)] at hchar
      have hpower := Real.rpow_le_rpow (abs_nonneg value) habsolute hregularity
      have hscaled := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpower (by positivity : 0 ≤ 2 * Real.pi + 2))
        (Real.rpow_nonneg (abs_nonneg frequency) regularity)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (transportMollifier_nonneg hscale value)]
      apply mul_le_mul_of_nonneg_right _ (transportMollifier_nonneg hscale value)
      exact hchar.trans (by simpa only [mul_assoc] using hscaled)
  rw [hidentity]
  apply (norm_integral_le_integral_norm _).trans
  have hdifference := hintegrand.sub hcomplex
  have hnormIntegrable : Integrable (fun value : ℝ =>
      ‖((Real.fourierChar (-(value * frequency)) : ℂ) - 1) * transportMollifier scale value‖) := by
    convert hdifference.norm using 1
    funext value
    simp only [Pi.sub_apply, mul_comm]
    congr 1
    ring
  calc
    _ ≤ ∫ value : ℝ, ((2 * Real.pi + 2) * scale ^ regularity * |frequency| ^ regularity) *
        transportMollifier scale value := integral_mono hnormIntegrable (hreal.const_mul _) hpointwise
    _ = _ := by rw [integral_const_mul, integral_transportMollifier hscale, mul_one]

end LambdaCantor.AE
