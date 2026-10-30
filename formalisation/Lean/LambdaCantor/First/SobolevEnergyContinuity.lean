import LambdaCantor.First.RootsMeasures
import LambdaCantor.ParameterContinuity
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace LambdaCantor.First.Roots

/-- Fatou's lemma turns pointwise continuous nonnegative energy integrands
into a lower semicontinuous extended energy, without assuming integrability. -/
theorem lowerSemicontinuous_lintegral_of_continuous
    {Parameter Frequency : Type*} [TopologicalSpace Parameter]
    [FirstCountableTopology Parameter] [MeasurableSpace Frequency]
    (measure : Measure Frequency) (integrand : Parameter → Frequency → ℝ≥0∞)
    (measurable : ∀ parameter, Measurable (integrand parameter))
    (continuous : ∀ frequency, Continuous (fun parameter => integrand parameter frequency)) :
    LowerSemicontinuous (fun parameter => ∫⁻ frequency, integrand parameter frequency ∂measure) := by
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro parameter
  calc
    _ = ∫⁻ frequency, liminf (fun point => integrand point frequency) (nhds parameter) ∂measure := by
      apply lintegral_congr
      intro frequency
      exact (continuous frequency).continuousAt.tendsto.liminf_eq.symm
    _ ≤ _ := lintegral_liminf_le measurable

theorem continuous_characteristic_compact_family
    {Parameter Address : Type*} [TopologicalSpace Parameter]
    [FirstCountableTopology Parameter] [LocallyCompactSpace Parameter]
    [TopologicalSpace Address] [CompactSpace Address] [SecondCountableTopology Address]
    [MeasurableSpace Address] [BorelSpace Address]
    (measure : Measure Address) [IsFiniteMeasure measure]
    (coordinate : Parameter → Address → ℝ) (joint : Continuous coordinate.uncurry) :
    Continuous (fun point : Parameter × ℝ => charFun (measure.map (coordinate point.1)) point.2) := by
  have integrand_continuous : Continuous
      (fun point : (Parameter × ℝ) × Address =>
        Complex.exp (((point.1.2 * coordinate point.1.1 point.2 : ℝ) : ℂ) * Complex.I)) := by
    have coordinates : Continuous (fun point : (Parameter × ℝ) × Address =>
        coordinate point.1.1 point.2) :=
      joint.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    exact ((Complex.continuous_ofReal.comp
      ((continuous_snd.comp continuous_fst).mul coordinates)).mul continuous_const).cexp
  have integral_continuous := continuous_parametric_integral_of_continuous
    (μ := measure) (f := fun point : Parameter × ℝ => fun address : Address =>
      Complex.exp (((point.2 * coordinate point.1 address : ℝ) : ℂ) * Complex.I))
    integrand_continuous isCompact_univ
  simp only [Measure.restrict_univ] at integral_continuous
  convert! integral_continuous using 1
  funext point
  have coordinate_measurable : Measurable (coordinate point.1) := by
    have fixed_continuous : Continuous (fun address : Address => coordinate point.1 address) :=
      joint.comp ((continuous_const : Continuous (fun _ : Address => point.1)).prodMk continuous_id)
    exact fixed_continuous.measurable
  rw [charFun_apply_real, integral_map_of_stronglyMeasurable
    coordinate_measurable (by fun_prop)]
  simp only [Function.comp_apply, Complex.ofReal_mul]

def projectedRootModel (parameter : ℝ × ℝ) (digits : ℕ → Bool × Bool) : ℝ :=
  parameter.2 * address parameter.1 (fun index => (digits index).1) +
    address parameter.1 (fun index => (digits index).2)

theorem continuous_projectedRootModel_band {lower upper : ℝ}
    (nonnegative : 0 ≤ lower) (less_one : upper < 1) (ordered : lower ≤ upper) :
    Continuous (fun point : (Set.Icc lower upper × ℝ) × (ℕ → Bool × Bool) =>
      projectedRootModel (point.1.1, point.1.2) point.2) := by
  have base := continuous_address_band nonnegative less_one ordered
  have first_digits : Continuous (fun digits : ℕ → Bool × Bool => fun index => (digits index).1) :=
    continuous_pi (fun index => continuous_fst.comp (continuous_apply index))
  have second_digits : Continuous (fun digits : ℕ → Bool × Bool => fun index => (digits index).2) :=
    continuous_pi (fun index => continuous_snd.comp (continuous_apply index))
  exact ((continuous_snd.comp continuous_fst).mul
    (base.comp ((continuous_fst.comp continuous_fst).prodMk (first_digits.comp continuous_snd)))).add
    (base.comp ((continuous_fst.comp continuous_fst).prodMk (second_digits.comp continuous_snd)))

def projectedSobolevEnergy (order : ℝ) (parameter : ℝ × ℝ) : ℝ≥0∞ :=
  ∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ order *
    ‖charFun (pairedAddressMeasure.map (projectedRootModel parameter)) frequency‖ ^ 2)

/-- The actual projected Cantor-law energy has closed bounded sublevel sets
on compact parameter bands. No density or Sobolev bound is assumed here. -/
theorem lowerSemicontinuous_projectedSobolevEnergy_band {lower upper : ℝ}
    (nonnegative : 0 ≤ lower) (less_one : upper < 1) (ordered : lower ≤ upper) (order : ℝ) :
    LowerSemicontinuous (fun parameter : Set.Icc lower upper × ℝ =>
      projectedSobolevEnergy order (parameter.1, parameter.2)) := by
  have characteristic := continuous_characteristic_compact_family pairedAddressMeasure
    (fun parameter : Set.Icc lower upper × ℝ =>
      projectedRootModel (parameter.1, parameter.2))
    (continuous_projectedRootModel_band nonnegative less_one ordered)
  apply lowerSemicontinuous_lintegral_of_continuous volume
  · intro parameter
    have continuous_frequency : Continuous (fun frequency : ℝ =>
        charFun (pairedAddressMeasure.map (projectedRootModel (parameter.1, parameter.2))) frequency) :=
      characteristic.comp ((continuous_const : Continuous (fun _ : ℝ => parameter)).prodMk continuous_id)
    have weight : Continuous (fun frequency : ℝ => (1 + frequency ^ 2) ^ order) := by
      apply Continuous.rpow_const (continuous_const.add (continuous_id.pow 2))
      intro frequency
      exact Or.inl (ne_of_gt (show 0 < (1 : ℝ) + frequency ^ 2 by positivity))
    exact (ENNReal.continuous_ofReal.comp (weight.mul (continuous_frequency.norm.pow 2))).measurable
  · intro frequency
    exact ENNReal.continuous_ofReal.comp
      (continuous_const.mul ((characteristic.comp (continuous_id.prodMk continuous_const)).norm.pow 2))

end LambdaCantor.First.Roots

