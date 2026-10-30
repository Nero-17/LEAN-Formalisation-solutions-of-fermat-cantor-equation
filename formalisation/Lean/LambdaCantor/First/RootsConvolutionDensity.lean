import LambdaCantor.First.RootsYoung
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.WithDensity

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace LambdaCantor.First.Roots

/-- Tonelli and translation invariance identify the convolution density even
when the second factor is singular. No Fourier inversion is needed. -/
theorem convolution_withDensity (measure : Measure ℝ) [SFinite measure]
    (density : ℝ → ℝ≥0∞) (measurable : Measurable density) :
    (volume.withDensity density) ∗ measure =
      volume.withDensity (fun point => ∫⁻ shift, density (point - shift) ∂measure) := by
  apply Measure.ext_of_lintegral
  intro test test_measurable
  have joint_measurable : Measurable (fun point : ℝ × ℝ => density (point.1 - point.2)) :=
    measurable.comp (by fun_prop)
  rw [Measure.lintegral_conv test_measurable,
    lintegral_withDensity_eq_lintegral_mul volume measurable (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul volume
      joint_measurable.lintegral_prod_right' test_measurable]
  simp only [Pi.mul_apply]
  calc
    (∫⁻ point, density point * ∫⁻ shift, test (point + shift) ∂measure) =
        ∫⁻ point, ∫⁻ shift, density point * test (point + shift) ∂measure := by
      apply lintegral_congr
      intro point
      rw [lintegral_const_mul _ (by fun_prop)]
    _ = ∫⁻ shift, ∫⁻ point, density point * test (point + shift) ∂volume ∂measure := by
      exact lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ shift, ∫⁻ point, density (point - shift) * test point ∂volume ∂measure := by
      apply lintegral_congr
      intro shift
      simpa only [sub_add_cancel] using
        (lintegral_sub_right_eq_self (fun point => density point * test (point + shift)) shift).symm
    _ = ∫⁻ point, ∫⁻ shift, density (point - shift) * test point ∂measure := by
      exact lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ point, (∫⁻ shift, density (point - shift) ∂measure) * test point := by
      apply lintegral_congr
      intro point
      exact lintegral_mul_const _ (by fun_prop)

/-- For an integrable nonnegative density the ENNReal formula agrees almost
everywhere with the ordinary real averaged density. -/
theorem convolution_withDensity_ofReal (measure : Measure ℝ) [IsProbabilityMeasure measure]
    (density : ℝ → ℝ) (nonnegative : ∀ point, 0 ≤ density point)
    (measurable : Measurable density) (integrable : Integrable density volume) :
    (volume.withDensity (fun point => ENNReal.ofReal (density point))) ∗ measure =
      volume.withDensity (fun point => ENNReal.ofReal (∫ shift, density (point - shift) ∂measure)) := by
  rw [convolution_withDensity measure _ (by fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [(translated_function_integrable measure density measurable integrable).prod_right_ae]
    with point section_integrable
  exact (ofReal_integral_eq_lintegral_ofReal section_integrable
    (Filter.Eventually.of_forall (fun shift => nonnegative (point - shift)))).symm

/-- The explicit averaged density is measurable, nonnegative and in L1 and
L2, and represents the actual convolution measure. -/
theorem convolution_has_l2_density (measure : Measure ℝ) [IsProbabilityMeasure measure]
    (density : ℝ → ℝ) (nonnegative : ∀ point, 0 ≤ density point)
    (measurable : Measurable density) (integrable : Integrable density volume)
    (square_integrable : MemLp density 2 volume) :
    ∃ averagedDensity : ℝ → ℝ,
      (∀ point, 0 ≤ averagedDensity point) ∧ Measurable averagedDensity ∧
      Integrable averagedDensity volume ∧ MemLp averagedDensity 2 volume ∧
      (volume.withDensity (fun point => ENNReal.ofReal (density point))) ∗ measure =
        volume.withDensity (fun point => ENNReal.ofReal (averagedDensity point)) := by
  refine ⟨fun point => ∫ shift, density (point - shift) ∂measure, ?_, ?_,
    translated_average_integrable measure density measurable integrable,
    translated_average_memLp_two measure density measurable square_integrable,
    convolution_withDensity_ofReal measure density nonnegative measurable integrable⟩
  · intro point
    exact integral_nonneg (fun shift => nonnegative (point - shift))
  · exact (measurable.comp (show Measurable (fun point : ℝ × ℝ => point.1 - point.2)
      from by fun_prop)).stronglyMeasurable.integral_prod_right'.measurable

end LambdaCantor.First.Roots
