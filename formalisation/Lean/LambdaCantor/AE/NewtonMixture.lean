import LambdaCantor.AE.PrefixTailLaw
import LambdaCantor.AE.CenteredNewtonCoefficients
import LambdaCantor.AE.PairedAddressStreams

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace LambdaCantor.AE

/-- All numerical data of one actual frozen Newton kernel. -/
structure FrozenNewtonKernel where
  freezing : ℝ
  residual : ℝ
  parameterDerivative : ℝ
  firstCoefficient : ℝ
  secondCoefficient : ℝ

def FrozenNewtonKernel.value (kernel : FrozenNewtonKernel) (digits : ℕ → Bool × Bool) : ℝ :=
  centeredNewtonValue kernel.freezing kernel.residual kernel.parameterDerivative
    kernel.firstCoefficient kernel.secondCoefficient
    (address kernel.freezing (fun index => (digits index).1))
    (address kernel.freezing (fun index => (digits index).2))

def FrozenNewtonKernel.law (kernel : FrozenNewtonKernel) : Measure ℝ :=
  centeredNewtonLaw kernel.freezing kernel.freezing kernel.residual kernel.parameterDerivative
    kernel.firstCoefficient kernel.secondCoefficient

theorem FrozenNewtonKernel.value_measurable (kernel : FrozenNewtonKernel) : Measurable kernel.value := by
  have first := (measurable_address_digits kernel.freezing).comp
    (show Measurable (fun digits : ℕ → Bool × Bool => fun index => (digits index).1) by fun_prop)
  have second := (measurable_address_digits kernel.freezing).comp
    (show Measurable (fun digits : ℕ → Bool × Bool => fun index => (digits index).2) by fun_prop)
  exact measurable_const.sub (((measurable_const.add (first.const_mul _)).add
    (second.const_mul _)).div_const _)

theorem FrozenNewtonKernel.law_eq_paired_map (kernel : FrozenNewtonKernel) :
    kernel.law = First.Roots.pairedAddressMeasure.map kernel.value := by
  have product_law :
      First.Roots.pairedAddressMeasure.map (fun digits : ℕ → Bool × Bool =>
        ((fun index => (digits index).1), (fun index => (digits index).2))) =
      addressProbability.prod addressProbability := by
    exact paired_address_streams_product_law
  unfold FrozenNewtonKernel.law
  rw [centeredNewtonLaw_eq_address_map, ← product_law,
    Measure.map_map (by
      have first : Measurable (fun digits : (ℕ → Bool) × (ℕ → Bool) =>
          address kernel.freezing digits.1) :=
        (measurable_address_digits kernel.freezing).comp measurable_fst
      have second : Measurable (fun digits : (ℕ → Bool) × (ℕ → Bool) =>
          address kernel.freezing digits.2) :=
        (measurable_address_digits kernel.freezing).comp measurable_snd
      exact measurable_const.sub (((measurable_const.add (first.const_mul _)).add
        (second.const_mul _)).div_const _)) (by fun_prop)]
  rfl

/-- The baseline is the genuine centered residual with the two remaining
tails set to zero and a fixed paired prefix. -/
def centeredPrefixBaseline (exponent : ℝ) (horizontalDepth verticalDepth tailDepth depth : ℕ)
    (word : Fin depth → Bool × Bool) (ratio : ℝ) : ℝ :=
  centeredTailResidual exponent horizontalDepth verticalDepth tailDepth ratio
    (address ratio (fun index => if before : index < depth then (word ⟨index, before⟩).1 else false))
    (address ratio (fun index => if before : index < depth then (word ⟨index, before⟩).2 else false))

def centeredFrozenNewton (exponent : ℝ) (horizontalDepth verticalDepth tailDepth depth : ℕ)
    (word : Fin depth → Bool × Bool) (freezing : ℝ) : FrozenNewtonKernel where
  freezing := freezing
  residual := centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word freezing
  parameterDerivative := deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word) freezing
  firstCoefficient := centeredNewtonFirstCoefficient exponent tailDepth depth freezing
    (address freezing (fun index => if before : index < depth then (word ⟨index, before⟩).1 else false))
  secondCoefficient := centeredNewtonSecondCoefficient exponent horizontalDepth verticalDepth tailDepth depth freezing
    (address freezing (fun index => if before : index < depth then (word ⟨index, before⟩).2 else false))

def newtonMixtureObservable (depth : ℕ)
    (kernels : (Fin depth → Bool × Bool) → FrozenNewtonKernel) (digits : ℕ → Bool × Bool) : ℝ :=
  (kernels (fun index => digits index)).value (fun index => digits (index + depth))

theorem newtonMixtureObservable_measurable (depth : ℕ)
    (kernels : (Fin depth → Bool × Bool) → FrozenNewtonKernel) :
    Measurable (newtonMixtureObservable depth kernels) := by
  have combine_measurable : Measurable
      (fun pair : (Fin depth → Bool × Bool) × (ℕ → Bool × Bool) => (kernels pair.1).value pair.2) :=
    measurable_from_prod_countable_right (fun word => (kernels word).value_measurable)
  have split_measurable : Measurable (fun digits : ℕ → Bool × Bool =>
      ((fun index : Fin depth => digits index), fun index : ℕ => digits (index + depth))) := by fun_prop
  change Measurable
    ((fun pair : (Fin depth → Bool × Bool) × (ℕ → Bool × Bool) =>
      (kernels pair.1).value pair.2) ∘
      (fun digits : ℕ → Bool × Bool =>
        ((fun index : Fin depth => digits index), fun index : ℕ => digits (index + depth))))
  exact combine_measurable.comp split_measurable

/-- The actual finite mixture in the paper is the law of one observable on
the original paired Bernoulli source. This supplies the common source needed
to identify its L1 limit by the same-address Newton estimate. -/
theorem newtonMixtureObservable_law (depth : ℕ)
    (kernels : (Fin depth → Bool × Bool) → FrozenNewtonKernel) :
    First.Roots.pairedAddressMeasure.map (newtonMixtureObservable depth kernels) =
      ∑ word : Fin depth → Bool × Bool, ((4 : ℝ≥0∞)⁻¹ ^ depth) • (kernels word).law := by
  have combine_measurable : Measurable
      (fun pair : (Fin depth → Bool × Bool) × (ℕ → Bool × Bool) => (kernels pair.1).value pair.2) :=
    measurable_from_prod_countable_right (fun word => (kernels word).value_measurable)
  change First.Roots.pairedAddressMeasure.map
    (fun digits : ℕ → Bool × Bool =>
      (fun pair : (Fin depth → Bool × Bool) × (ℕ → Bool × Bool) =>
        (kernels pair.1).value pair.2)
        ((fun index : Fin depth => digits index), fun index : ℕ => digits (index + depth))) =
      ∑ word : Fin depth → Bool × Bool, ((4 : ℝ≥0∞)⁻¹ ^ depth) • (kernels word).law
  rw [paired_prefix_observable_law depth _ combine_measurable]
  apply Finset.sum_congr rfl
  intro word _
  rw [(kernels word).law_eq_paired_map]

end LambdaCantor.AE
