import LambdaCantor.AE.SobolevTransportMollification

noncomputable section
open Set Metric MeasureTheory Convolution Filter
open scoped ENNReal FourierTransform

namespace LambdaCantor.AE

theorem bounded_support_L1_le_L2 {function : ℝ → ℝ} {radius : ℝ}
    (hradius : 0 ≤ radius) (hLp : MemLp function 2 volume)
    (hsupport : Function.support function ⊆ Icc (-radius) radius) :
    (∫ value : ℝ, |function value|) ≤
      Real.sqrt (2 * radius) * Real.sqrt (∫ value : ℝ, |function value| ^ 2) := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (-radius) radius)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
  have hzero (value : ℝ) (hvalue : value ∉ Icc (-radius) radius) : function value = 0 := by
    by_contra hnonzero
    exact hvalue (hsupport hnonzero)
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := volume.restrict (Icc (-radius) radius))
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    (show MemLp function (ENNReal.ofReal 2) (volume.restrict (Icc (-radius) radius)) by
      simpa using hLp.restrict (Icc (-radius) radius))
    (show MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2)
        (volume.restrict (Icc (-radius) radius)) from memLp_const 1)
  simp only [Real.rpow_two, Real.norm_eq_abs, abs_one, mul_one, one_pow] at hholder
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun value hvalue => by rw [hzero value hvalue, abs_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun value hvalue => by rw [hzero value hvalue, abs_zero, zero_pow (by norm_num)]),
    integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one,
    measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at hholder
  simpa only [sub_neg_eq_add, ← two_mul, ← Real.sqrt_eq_rpow, mul_comm] using hholder

theorem support_mollification_error_subset {density : ℝ → ℝ} {radius scale : ℝ}
    (hscale : 0 < scale) (hsupport : Function.support density ⊆ Icc (-radius) radius) :
    Function.support (fun value => density value - mollifyDensity density scale value) ⊆
      Icc (-(radius + scale)) (radius + scale) := by
  intro value hvalue
  by_contra houtside
  have hdensityZero : density value = 0 := by
    by_contra hnonzero
    have hinside := hsupport hnonzero
    exact houtside ⟨by linarith [hinside.1], by linarith [hinside.2]⟩
  have hmollifiedZero : mollifyDensity density scale value = 0 := by
    unfold mollifyDensity
    rw [convolution_def]
    apply integral_eq_zero_of_ae
    apply Eventually.of_forall
    intro location
    change density location * transportMollifier scale (value - location) = 0
    by_cases hzero : density location = 0
    · rw [hzero, zero_mul]
    · have hlocation := hsupport hzero
      have hkernel : transportMollifier scale (value - location) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have hinterval := tsupport_transportMollifier_subset hscale hmem
        exact houtside ⟨by linarith [hlocation.1, hinterval.1],
          by linarith [hlocation.2, hinterval.2]⟩
      rw [hkernel, mul_zero]
  exact hvalue (by
    change density value - mollifyDensity density scale value = 0
    rw [hdensityZero, hmollifiedZero, sub_self])

/-- Bounded support converts the actual Fourier-derived L2 smoothing error
into the first term C A t^σ of the transport interpolation argument. -/
theorem mollification_L1_error_bound {density : ℝ → ℝ} {radius scale regularity bound : ℝ}
    (hdensity : Integrable density) (hradius : 0 ≤ radius) (hscale : 0 < scale)
    (hscaleOne : scale ≤ 1) (hregularity : 0 ≤ regularity) (hregularityOne : regularity ≤ 1)
    (hbound : 0 ≤ bound) (hsupport : Function.support density ⊆ Icc (-radius) radius)
    (henergy : (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) *
      ‖𝓕 (fun value => (density value : ℂ)) frequency‖ ^ 2)) ≤ ENNReal.ofReal (bound ^ 2)) :
    (∫ value : ℝ, |density value - mollifyDensity density scale value|) ≤
      (Real.sqrt (2 * (radius + 1)) * (2 * Real.pi + 2)) * bound * scale ^ regularity := by
  obtain ⟨hLp, hphysical⟩ := mollification_error_memLp_and_energy_bound hdensity hscale
    hregularity hregularityOne (henergy.trans_lt ENNReal.ofReal_lt_top)
  have hphysicalBound := hphysical.trans
    (mul_le_mul_left' henergy (ENNReal.ofReal (((2 * Real.pi + 2) * scale ^ regularity) ^ 2)))
  rw [← ENNReal.ofReal_mul (sq_nonneg _)] at hphysicalBound
  have hsquare := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) (sq_nonneg _))).mp hphysicalBound
  have hsqrt := Real.sqrt_le_sqrt hsquare
  have hproduct : ((2 * Real.pi + 2) * scale ^ regularity) ^ 2 * bound ^ 2 =
      ((2 * Real.pi + 2) * scale ^ regularity * bound) ^ 2 := by ring
  rw [hproduct, Real.sqrt_sq (by positivity)] at hsqrt
  have hfirst := bounded_support_L1_le_L2 (by positivity : 0 ≤ radius + scale) hLp
    (support_mollification_error_subset hscale hsupport)
  have hlength : Real.sqrt (2 * (radius + scale)) ≤ Real.sqrt (2 * (radius + 1)) :=
    Real.sqrt_le_sqrt (by linarith)
  apply hfirst.trans
  have hresult := mul_le_mul hlength hsqrt (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  convert hresult using 1 <;> ring

end LambdaCantor.AE
