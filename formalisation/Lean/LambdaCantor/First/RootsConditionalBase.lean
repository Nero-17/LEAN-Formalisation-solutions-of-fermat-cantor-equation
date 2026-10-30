import LambdaCantor.First.RootFibreTopology
import Mathlib.Probability.Kernel.CondDistrib

/-! Actual conditional address laws over the selected root. No absolute
continuity or conditional dimension hypothesis is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
namespace LambdaCantor.First.Roots

/-- The regular conditional law of the original address given its actual root. -/
def rootConditional {exponent : ℝ} (data : RootFibreData exponent) :
    Kernel ℝ (ℕ → Bool × Bool) :=
  condDistrib id data.root pairedAddressMeasure

instance rootConditional_markov {exponent : ℝ} (data : RootFibreData exponent) :
    IsMarkovKernel (rootConditional data) := by
  unfold rootConditional
  infer_instance

/-- Disintegration of the actual graph law, with the actual root pushforward. -/
theorem rootConditional_compProd {exponent : ℝ} (data : RootFibreData exponent) :
    rootLaw data.root ⊗ₘ rootConditional data =
      pairedAddressMeasure.map (fun digits => (data.root digits, digits)) := by
  exact compProd_map_condDistrib aemeasurable_id

/-- Integrating the conditional laws recovers the original address measure. -/
theorem rootConditional_comp {exponent : ℝ} (data : RootFibreData exponent) :
    rootConditional data ∘ₘ rootLaw data.root = pairedAddressMeasure := by
  simpa only [rootConditional, rootLaw, Measure.map_id] using
    (condDistrib_comp_map (rootFibreData_continuous_root data).measurable.aemeasurable
      (Y := id) aemeasurable_id)

/-- Tonelli identity for an arbitrary measurable nonnegative graph observable. -/
theorem rootConditional_lintegral {exponent : ℝ} (data : RootFibreData exponent)
    (observable : ℝ × (ℕ → Bool × Bool) → ℝ≥0∞) (hmeasurable : Measurable observable) :
    (∫⁻ parameter, ∫⁻ digits, observable (parameter, digits) ∂rootConditional data parameter
      ∂rootLaw data.root) =
        ∫⁻ digits, observable (data.root digits, digits) ∂pairedAddressMeasure := by
  letI := rootFibreData_rootLaw_probability data
  rw [← Measure.lintegral_compProd hmeasurable, rootConditional_compProd]
  exact lintegral_map hmeasurable
    ((rootFibreData_continuous_root data).measurable.prodMk measurable_id)

/-- The Bochner version for every integrable observable of the graph law. -/
theorem rootConditional_integral {exponent : ℝ} (data : RootFibreData exponent)
    (observable : ℝ × (ℕ → Bool × Bool) → ℝ)
    (hintegrable : Integrable observable
      (pairedAddressMeasure.map (fun digits => (data.root digits, digits)))) :
    (∫ parameter, ∫ digits, observable (parameter, digits) ∂rootConditional data parameter
      ∂rootLaw data.root) =
        ∫ digits, observable (data.root digits, digits) ∂pairedAddressMeasure := by
  letI := rootFibreData_rootLaw_probability data
  have hcomp : Integrable observable (rootLaw data.root ⊗ₘ rootConditional data) := by
    rwa [rootConditional_compProd]
  rw [← Measure.integral_compProd hcomp, rootConditional_compProd]
  exact integral_map
    ((rootFibreData_continuous_root data).measurable.prodMk measurable_id).aemeasurable
    hintegrable.aestronglyMeasurable

/-- Almost every conditional law is supported on its actual selected-root fibre. -/
theorem rootConditional_ae_fibre {exponent : ℝ} (data : RootFibreData exponent) :
    ∀ᵐ parameter ∂rootLaw data.root,
      ∀ᵐ digits ∂rootConditional data parameter, data.root digits = parameter := by
  letI := rootFibreData_rootLaw_probability data
  apply Measure.ae_ae_of_ae_compProd
    (μ := rootLaw data.root) (κ := rootConditional data)
    (p := fun pair : ℝ × (ℕ → Bool × Bool) => data.root pair.2 = pair.1)
  rw [rootConditional_compProd]
  apply (ae_map_iff
    ((rootFibreData_continuous_root data).measurable.prodMk measurable_id).aemeasurable
    (measurableSet_eq_fun
      ((rootFibreData_continuous_root data).measurable.comp measurable_snd)
      measurable_fst)).mpr
  exact Filter.Eventually.of_forall (fun _ => rfl)

end LambdaCantor.First.Roots
