import LambdaCantor.AE.SobolevTransportMollifier
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set Metric MeasureTheory

namespace LambdaCantor.AE

theorem transportMollifier_translation_L1_le_two {scale : ℝ} (hscale : 0 < scale)
    (first second : ℝ) :
    (∫ value : ℝ, |transportMollifier scale (value - first) -
      transportMollifier scale (value - second)|) ≤ 2 := by
  have hfirst := (integrable_transportMollifier hscale).comp_sub_right first
  have hsecond := (integrable_transportMollifier hscale).comp_sub_right second
  calc
    _ ≤ ∫ value : ℝ, |transportMollifier scale (value - first)| +
        |transportMollifier scale (value - second)| :=
      integral_mono (hfirst.sub hsecond).abs (hfirst.abs.add hsecond.abs)
        (fun value => by
          simpa using (abs_sub_le (transportMollifier scale (value - first)) 0
            (transportMollifier scale (value - second))))
    _ = 2 := by
      rw [integral_add hfirst.abs hsecond.abs,
        integral_sub_right_eq_self (fun value : ℝ => |transportMollifier scale value|) first,
        integral_sub_right_eq_self (fun value : ℝ => |transportMollifier scale value|) second,
        integral_abs_transportMollifier hscale]
      norm_num

theorem transportMollifier_translation_small_bound
    {constant scale : ℝ} (hconstant : 0 < constant) (hscale : 0 < scale)
    (hderivative : ∀ value : ℝ, |deriv (transportMollifier scale) value| ≤ constant / scale ^ 2)
    (first second : ℝ) (hsmall : |first - second| ≤ scale) :
    (∫ value : ℝ, |transportMollifier scale (value - first) -
      transportMollifier scale (value - second)|) ≤
      4 * constant * |first - second| / scale := by
  have hlipschitz : LipschitzWith (NNReal.mk (constant / scale ^ 2) (by positivity))
      (transportMollifier scale) := by
    apply lipschitzWith_of_nnnorm_deriv_le
      ((contDiff_transportMollifier scale).differentiable (by simp))
    intro value
    exact_mod_cast hderivative value
  have hpointwise (value : ℝ) :
      |transportMollifier scale (value - first) - transportMollifier scale (value - second)| ≤
        constant / scale ^ 2 * |first - second| := by
    have hbound := hlipschitz.dist_le_mul (value - first) (value - second)
    simpa only [NNReal.coe_mk, Real.dist_eq, show value - first - (value - second) = -(first - second) by ring,
      abs_neg] using hbound
  have hsupport : Function.support (fun value : ℝ =>
      transportMollifier scale (value - first) - transportMollifier scale (value - second)) ⊆
      Icc (first - 2 * scale) (first + 2 * scale) := by
    intro value hvalue
    by_contra houtside
    have hfirst : transportMollifier scale (value - first) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have hinterval := tsupport_transportMollifier_subset hscale hmem
      apply houtside
      constructor <;> linarith [hinterval.1, hinterval.2]
    have hsecond : transportMollifier scale (value - second) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have hinterval := tsupport_transportMollifier_subset hscale hmem
      have hdifference := abs_le.mp hsmall
      apply houtside
      constructor <;> linarith [hinterval.1, hinterval.2, hdifference.1, hdifference.2]
    exact hvalue (by simp only [hfirst, hsecond, sub_self])
  have hmajorant (value : ℝ) :
      |transportMollifier scale (value - first) - transportMollifier scale (value - second)| ≤
      (Icc (first - 2 * scale) (first + 2 * scale)).indicator
        (fun _ => constant / scale ^ 2 * |first - second|) value := by
    by_cases hvalue : value ∈ Icc (first - 2 * scale) (first + 2 * scale)
    · rw [indicator_of_mem hvalue]
      exact hpointwise value
    · rw [indicator_of_notMem hvalue]
      have hzero : transportMollifier scale (value - first) -
          transportMollifier scale (value - second) = 0 := by
        by_contra hnonzero
        exact hvalue (hsupport hnonzero)
      simp only [hzero, abs_zero, le_refl]
  have hintegrable := ((integrable_transportMollifier hscale).comp_sub_right first).sub
    ((integrable_transportMollifier hscale).comp_sub_right second)
  have hmajorantIntegrable : Integrable
      ((Icc (first - 2 * scale) (first + 2 * scale)).indicator
        (fun _ : ℝ => constant / scale ^ 2 * |first - second|)) :=
    (integrableOn_const (isCompact_Icc.measure_ne_top (μ := volume))).integrable_indicator measurableSet_Icc
  calc
    _ ≤ ∫ value : ℝ, (Icc (first - 2 * scale) (first + 2 * scale)).indicator
        (fun _ => constant / scale ^ 2 * |first - second|) value :=
      integral_mono hintegrable.abs hmajorantIntegrable hmajorant
    _ = _ := by
      rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul,
        measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      field_simp [hscale.ne']
      ring

/-- The actual mollifier has the sharp inverse-scale transport cost needed
for the paper's smoothing optimization. -/
theorem exists_transportMollifier_translation_bound :
    ∃ constant : ℝ, 0 < constant ∧ ∀ scale : ℝ, 0 < scale → ∀ first second : ℝ,
      (∫ value : ℝ, |transportMollifier scale (value - first) -
        transportMollifier scale (value - second)|) ≤ constant * |first - second| / scale := by
  obtain ⟨constant, hconstant, hderivative⟩ := exists_transportMollifier_derivative_bound
  refine ⟨4 * constant + 2, by positivity, ?_⟩
  intro scale hscale first second
  by_cases hsmall : |first - second| ≤ scale
  · apply (transportMollifier_translation_small_bound hconstant hscale
      (hderivative scale hscale) first second hsmall).trans
    apply (div_le_div_iff_of_pos_right hscale).mpr
    nlinarith [abs_nonneg (first - second)]
  · apply (transportMollifier_translation_L1_le_two hscale first second).trans
    apply (le_div_iff₀ hscale).mpr
    have hproduct := mul_nonneg hconstant.le (abs_nonneg (first - second))
    nlinarith

end LambdaCantor.AE
