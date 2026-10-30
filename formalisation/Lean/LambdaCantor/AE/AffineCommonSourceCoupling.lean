import LambdaCantor.AE.CommonSourceCoupling
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory

namespace LambdaCantor.AE

theorem affine_common_source_cost
    {Sample : Type*} [MeasurableSpace Sample]
    (source : Measure Sample) [IsProbabilityMeasure source]
    {first second root : Sample → ℝ} {firstError secondError width : ℝ} (origin : ℝ)
    (width_positive : 0 < width)
    (first_measurable : Measurable first) (second_measurable : Measurable second)
    (first_error : ∀ sample, |first sample-root sample| ≤ firstError)
    (second_error : ∀ sample, |second sample-root sample| ≤ secondError) :
    Integrable (fun pair : ℝ × ℝ => |pair.1-pair.2|)
        (commonSourceCoupling source (fun sample => (first sample-origin)/width)
          (fun sample => (second sample-origin)/width)) ∧
      (∫ pair : ℝ × ℝ, |pair.1-pair.2|
        ∂commonSourceCoupling source (fun sample => (first sample-origin)/width)
          (fun sample => (second sample-origin)/width)) ≤ (firstError+secondError)/width := by
  have first_normalized : ∀ sample,
      |(first sample-origin)/width-(root sample-origin)/width| ≤ firstError/width := by
    intro sample
    have identity : (first sample-origin)/width-(root sample-origin)/width =
        (first sample-root sample)/width := by ring
    rw [identity, abs_div, abs_of_pos width_positive]
    exact div_le_div_of_nonneg_right (first_error sample) width_positive.le
  have second_normalized : ∀ sample,
      |(second sample-origin)/width-(root sample-origin)/width| ≤ secondError/width := by
    intro sample
    have identity : (second sample-origin)/width-(root sample-origin)/width =
        (second sample-root sample)/width := by ring
    rw [identity, abs_div, abs_of_pos width_positive]
    exact div_le_div_of_nonneg_right (second_error sample) width_positive.le
  obtain ⟨integrable, cost⟩ := commonSourceCoupling_cost_of_common_approximation source
    ((first_measurable.sub_const origin).div_const width)
    ((second_measurable.sub_const origin).div_const width) first_normalized second_normalized
  refine ⟨integrable, ?_⟩
  simpa only [add_div] using cost

end LambdaCantor.AE
