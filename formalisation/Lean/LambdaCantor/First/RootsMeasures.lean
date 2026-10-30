import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Tactic.NormNum

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace LambdaCantor.First.Roots

/-- Independent fair paired binary digits: the actual source probability in the
root-fibres construction, on a single four-symbol address space. -/
def pairedAddressMeasure : Measure (ℕ → Bool × Bool) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype (Bool × Bool)).toMeasure)

instance pairedAddressMeasure_probability : IsProbabilityMeasure pairedAddressMeasure := by
  unfold pairedAddressMeasure
  infer_instance

def pairedPrefix (digits : ℕ → Bool × Bool) (depth : ℕ) : Set (ℕ → Bool × Bool) :=
  {other | ∀ j < depth, other j = digits j}

/-- Exact mass of a paired cylinder. This supplies the weight used in the
incidence Frostman bound and all complete-kernel sums. -/
theorem pairedPrefix_mass (digits : ℕ → Bool × Bool) (depth : ℕ) :
    pairedAddressMeasure (pairedPrefix digits depth) = (1 / 4 : ℝ≥0∞) ^ depth := by
  have cylinder_identity : pairedPrefix digits depth =
      Set.pi (Finset.range depth) (fun j => {digits j}) := by
    ext other
    simp [pairedPrefix, Set.mem_pi]
  rw [cylinder_identity, pairedAddressMeasure,
    Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp [PMF.toMeasure_apply_singleton, measurableSet_singleton,
    PMF.uniformOfFintype_apply, Fintype.card_prod]

/-- The law of an actual address-to-root function. Measurability and absolute
continuity are mathematical obligations, not built into this definition. -/
def rootLaw (root : (ℕ → Bool × Bool) → ℝ) : Measure ℝ :=
  pairedAddressMeasure.map root

theorem rootLaw_probability (root : (ℕ → Bool × Bool) → ℝ)
    (root_measurable : Measurable root) : IsProbabilityMeasure (rootLaw root) :=
  Measure.isProbabilityMeasure_map root_measurable.aemeasurable

theorem rootLaw_parameter_band (root : (ℕ → Bool × Bool) → ℝ)
    (root_measurable : Measurable root) (lower upper : ℝ)
    (root_in_band : ∀ digits, root digits ∈ Set.Icc lower upper) :
    rootLaw root (Set.Icc lower upper) = 1 := by
  rw [rootLaw, Measure.map_apply root_measurable measurableSet_Icc]
  have preimage_univ : root ⁻¹' Set.Icc lower upper = Set.univ := by
    ext digits
    simp [root_in_band digits]
  rw [preimage_univ, measure_univ]

end LambdaCantor.First.Roots
