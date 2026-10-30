import LambdaCantor.First.LinearRegularityExternal
import LambdaCantor.First.SobolevEnergyContinuity
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

/-- Proposed classical external input, NOT an axiom or a proved theorem here.
The measure is a finite positive Borel measure on the real line. The Fourier
convention is exactly mathlib `charFun`: exp(i*frequency*point). The conclusion
includes a nonnegative measurable real density, its L1 and L2 integrability,
and equality of the actual measure with volume.withDensity(ofReal density).
Source verified by the coordinator: Fernando Román García, arXiv:1801.09022v3,
Theorem 1.2(1), PDF page 2, https://arxiv.org/pdf/1801.09022 .
The published Fourier convention has factor (2*pi)^(-1/2) and opposite sign;
reflection and a nonzero constant preserve L2. Compact support is retained. -/
def ClassicalL2FourierDensityStatement : Prop :=
  ∀ (measure : Measure ℝ) [IsFiniteMeasure measure],
    (∃ support : Set ℝ, IsCompact support ∧ measure supportᶜ = 0) →
    MemLp (charFun measure) 2 volume → LinearRegularity.HasL2Density measure

/-- The good-set energy condition supplies precisely the L2 hypothesis of the
classical converse. This implication is internal and uses no inversion input. -/
theorem characteristic_memLp_two_of_weighted_energy (measure : Measure ℝ) [IsFiniteMeasure measure]
    (order : ℝ) (order_nonnegative : 0 ≤ order)
    (finite_energy : (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ order *
      ‖charFun measure frequency‖ ^ 2)) ≠ ∞) : MemLp (charFun measure) 2 volume := by
  have comparison : (∫⁻ frequency : ℝ, ENNReal.ofReal (‖charFun measure frequency‖ ^ 2)) ≤
      ∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ order *
        ‖charFun measure frequency‖ ^ 2) := by
    apply lintegral_mono
    intro frequency
    apply ENNReal.ofReal_le_ofReal
    have weight := Real.one_le_rpow (show 1 ≤ 1 + frequency ^ 2 by nlinarith [sq_nonneg frequency]) order_nonnegative
    simpa only [one_mul] using mul_le_mul_of_nonneg_right weight (sq_nonneg ‖charFun measure frequency‖)
  have finite_integral : HasFiniteIntegral (fun frequency : ℝ => ‖charFun measure frequency‖ ^ 2) volume :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).2
      (comparison.trans_lt (lt_top_iff_ne_top.mpr finite_energy))
  apply (memLp_two_iff_integrable_sq_norm (stronglyMeasurable_charFun (μ := measure)).aestronglyMeasurable).2
  exact ⟨((measurable_charFun (μ := measure)).norm.pow_const 2).aestronglyMeasurable, finite_integral⟩

/-- Conditional only on the explicitly named classical converse, not on any
root-law density statement. No axiom is introduced by this theorem. -/
theorem hasL2Density_of_weighted_energy_of_classical_converse (classical_converse : ClassicalL2FourierDensityStatement)
    (measure : Measure ℝ) [IsFiniteMeasure measure]
    (compact_support : ∃ support : Set ℝ, IsCompact support ∧ measure supportᶜ = 0)
    (order : ℝ) (order_nonnegative : 0 ≤ order)
    (finite_energy : (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ order *
      ‖charFun measure frequency‖ ^ 2)) ≠ ∞) : LinearRegularity.HasL2Density measure :=
  classical_converse measure compact_support (characteristic_memLp_two_of_weighted_energy measure order order_nonnegative finite_energy)


/-- The actual projected law has compact support, as the continuous image of
the compact full paired-address space. This discharges the source hypothesis
of the proposed classical converse without restricting the fresh tails. -/
theorem projectedRootModel_compact_support {parameter : ℝ × ℝ}
    (nonnegative : 0 ≤ parameter.1) (less_one : parameter.1 < 1) :
    ∃ support : Set ℝ, IsCompact support ∧
      (pairedAddressMeasure.map (projectedRootModel parameter)) supportᶜ = 0 := by
  have address_continuous := continuous_address nonnegative less_one
  have model_continuous : Continuous (projectedRootModel parameter) :=
    (continuous_const.mul (address_continuous.comp (by fun_prop))).add
      (address_continuous.comp (by fun_prop))
  have compact_range : IsCompact (Set.range (projectedRootModel parameter)) :=
    isCompact_range model_continuous
  refine ⟨Set.range (projectedRootModel parameter), compact_range, ?_⟩
  rw [Measure.map_apply model_continuous.measurable compact_range.isClosed.measurableSet.compl]
  have empty_preimage : (projectedRootModel parameter) ⁻¹' (Set.range (projectedRootModel parameter))ᶜ = ∅ := by
    ext digits
    simp
  rw [empty_preimage, measure_empty]
end LambdaCantor.First.Roots


