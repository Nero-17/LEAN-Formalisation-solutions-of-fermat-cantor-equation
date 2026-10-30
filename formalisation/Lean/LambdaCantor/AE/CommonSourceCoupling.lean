import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Filter

namespace LambdaCantor.AE

def commonSourceCoupling {Sample : Type*} [MeasurableSpace Sample]
    (source : Measure Sample) (first second : Sample → ℝ) : Measure (ℝ × ℝ) :=
  source.map (fun sample => (first sample, second sample))

theorem commonSourceCoupling_fst {Sample : Type*} [MeasurableSpace Sample]
    (source : Measure Sample) {first second : Sample → ℝ}
    (first_measurable : Measurable first) (second_measurable : Measurable second) :
    (commonSourceCoupling source first second).map Prod.fst = source.map first := by
  rw [commonSourceCoupling, Measure.map_map measurable_fst (first_measurable.prodMk second_measurable)]
  rfl

theorem commonSourceCoupling_snd {Sample : Type*} [MeasurableSpace Sample]
    (source : Measure Sample) {first second : Sample → ℝ}
    (first_measurable : Measurable first) (second_measurable : Measurable second) :
    (commonSourceCoupling source first second).map Prod.snd = source.map second := by
  rw [commonSourceCoupling, Measure.map_map measurable_snd (first_measurable.prodMk second_measurable)]
  rfl

theorem commonSourceCoupling_probability {Sample : Type*} [MeasurableSpace Sample]
    (source : Measure Sample) [IsProbabilityMeasure source] {first second : Sample → ℝ}
    (first_measurable : Measurable first) (second_measurable : Measurable second) :
    IsProbabilityMeasure (commonSourceCoupling source first second) :=
  Measure.isProbabilityMeasure_map (first_measurable.prodMk second_measurable).aemeasurable

/-- Two actual observables approximating the same root give an actual
probability coupling with the sum of their errors as transport cost. -/
theorem commonSourceCoupling_cost_of_common_approximation
    {Sample : Type*} [MeasurableSpace Sample]
    (source : Measure Sample) [IsProbabilityMeasure source]
    {first second root : Sample → ℝ} {firstError secondError : ℝ}
    (first_measurable : Measurable first) (second_measurable : Measurable second)
    (first_error : ∀ sample, |first sample-root sample| ≤ firstError)
    (second_error : ∀ sample, |second sample-root sample| ≤ secondError) :
    Integrable (fun pair : ℝ × ℝ => |pair.1-pair.2|) (commonSourceCoupling source first second) ∧
      (∫ pair : ℝ × ℝ, |pair.1-pair.2| ∂commonSourceCoupling source first second) ≤ firstError+secondError := by
  have measurable : Measurable (fun sample : Sample => |first sample-second sample|) :=
    continuous_abs.measurable.comp (first_measurable.sub second_measurable)
  have pointwise : ∀ sample, |first sample-second sample| ≤ firstError+secondError := by
    intro sample
    have triangle := abs_sub_le (first sample) (root sample) (second sample)
    rw [abs_sub_comm (root sample) (second sample)] at triangle
    linarith [first_error sample, second_error sample]
  have source_integrable : Integrable (fun sample => |first sample-second sample|) source :=
    (integrable_const (firstError+secondError)).mono' measurable.aestronglyMeasurable
      (Eventually.of_forall (fun sample => by simpa only [Real.norm_eq_abs, abs_abs] using pointwise sample))
  have pair_measurable : Measurable (fun pair : ℝ × ℝ => |pair.1-pair.2|) :=
    continuous_abs.measurable.comp (measurable_fst.sub measurable_snd)
  refine ⟨(integrable_map_measure pair_measurable.aestronglyMeasurable
    (first_measurable.prodMk second_measurable).aemeasurable).mpr source_integrable, ?_⟩
  rw [commonSourceCoupling, integral_map (first_measurable.prodMk second_measurable).aemeasurable
    pair_measurable.aestronglyMeasurable]
  apply (integral_mono source_integrable (integrable_const _) pointwise).trans_eq
  simp

end LambdaCantor.AE
