import LambdaCantor.First.RootsConditionalDensities
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace LambdaCantor.First.Roots

def goodSetPrefixBadParameters {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound depth : ℕ) (word : Fin depth → Bool × Bool) (slack : ℝ) : Set ℝ :=
  {parameter | parameter ^ (-(depth : ℝ)) * Real.exp (slack * depth) <
    goodSetPrefixDensity data orderIndex bound depth word parameter}

def goodSetPrefixBadAddresses {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound depth : ℕ) (slack : ℝ) : Set (ℕ → Bool × Bool) :=
  ⋃ word : Fin depth → Bool × Bool, finitePairedPrefix word ∩
    data.root ⁻¹' goodSetPrefixBadParameters data orderIndex bound depth word slack

def goodSetPrefixTailTotal {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound : ℕ) (slack : ℝ) (depth : ℕ) : ℝ :=
  ∑ word : Fin depth → Bool × Bool, ((4 : ℝ)⁻¹ ^ depth) *
    ∫ parameter in goodSetPrefixBadParameters data orderIndex bound depth word slack,
      goodSetPrefixDensity data orderIndex bound depth word parameter

theorem measurableSet_goodSetPrefixBadParameters {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound depth : ℕ) (word : Fin depth → Bool × Bool) (slack : ℝ) :
    MeasurableSet (goodSetPrefixBadParameters data orderIndex bound depth word slack) := by
  apply measurableSet_lt
  · exact (measurable_id.pow_const _).mul measurable_const
  · exact (goodSetPrefixDensity_properties data orderIndex bound depth word).2.1

/-- The mass of each actual bad cylinder equals its weighted density tail. -/
theorem goodSetPrefixBadAddresses_mass_bound {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound : ℕ) (slack : ℝ) (depth : ℕ) :
    (pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound))
      (goodSetPrefixBadAddresses data orderIndex bound depth slack) ≤
      ENNReal.ofReal (goodSetPrefixTailTotal data orderIndex bound slack depth) := by
  classical
  let source := pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound)
  have branch (word : Fin depth → Bool × Bool) :
      source (finitePairedPrefix word ∩ data.root ⁻¹'
        goodSetPrefixBadParameters data orderIndex bound depth word slack) =
      ENNReal.ofReal (((4 : ℝ)⁻¹ ^ depth) *
        ∫ parameter in goodSetPrefixBadParameters data orderIndex bound depth word slack,
          goodSetPrefixDensity data orderIndex bound depth word parameter) := by
    have properties := goodSetPrefixDensity_properties data orderIndex bound depth word
    have bad_measurable := measurableSet_goodSetPrefixBadParameters data orderIndex bound depth word slack
    have mass := congrArg (fun measure : Measure ℝ => measure
      (goodSetPrefixBadParameters data orderIndex bound depth word slack))
      (goodSetPrefixDensity_law data orderIndex bound depth word)
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (rootFibreData_continuous_root data).measurable bad_measurable,
      Measure.restrict_apply ((rootFibreData_continuous_root data).measurable bad_measurable),
      withDensity_apply _ bad_measurable,
      ← ofReal_integral_eq_lintegral_ofReal properties.2.2.integrableOn
        (Filter.Eventually.of_forall properties.1)] at mass
    have cancellation := congrArg (fun value : ℝ≥0∞ => ((4 : ℝ≥0∞)⁻¹ ^ depth) * value) mass
    have inverse_identity : ((4 : ℝ≥0∞)⁻¹ ^ depth) * ((4 : ℝ≥0∞) ^ depth) = 1 := by
      rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by finiteness), one_pow]
    rw [← mul_assoc, inverse_identity, one_mul] at cancellation
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (4 : ℝ)⁻¹ ^ depth),
      ENNReal.ofReal_pow (by positivity : 0 ≤ (4 : ℝ)⁻¹),
      ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (4 : ℝ)),
      ENNReal.ofReal_ofNat]
    simpa only [source, Set.inter_comm] using cancellation
  calc
    _ ≤ ∑ word : Fin depth → Bool × Bool, source (finitePairedPrefix word ∩ data.root ⁻¹'
        goodSetPrefixBadParameters data orderIndex bound depth word slack) :=
      measure_iUnion_fintype_le source _
    _ = ∑ word : Fin depth → Bool × Bool, ENNReal.ofReal (((4 : ℝ)⁻¹ ^ depth) *
        ∫ parameter in goodSetPrefixBadParameters data orderIndex bound depth word slack,
          goodSetPrefixDensity data orderIndex bound depth word parameter) := by
      apply Finset.sum_congr rfl
      intro word _
      exact branch word
    _ = _ := by
      rw [goodSetPrefixTailTotal, ENNReal.ofReal_sum_of_nonneg]
      intro word _
      exact mul_nonneg (by positivity) (setIntegral_nonneg
        (measurableSet_goodSetPrefixBadParameters data orderIndex bound depth word slack)
        (fun _ _ => (goodSetPrefixDensity_properties data orderIndex bound depth word).1 _))

/-- Borel--Cantelli is applied to the actual source events, rather than to
independent model kernels. Its summability premise is the prefix-tail endpoint. -/
theorem goodSetPrefixDensity_eventually_of_summable_tails {exponent : ℝ}
    (data : RootFibreData exponent) (orderIndex bound : ℕ) (slack : ℝ)
    (summable : Summable (goodSetPrefixTailTotal data orderIndex bound slack)) :
    ∀ᵐ digits ∂pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound),
      ∀ᶠ depth in atTop, goodSetPrefixDensity data orderIndex bound depth
        (fun index : Fin depth => digits index) (data.root digits) ≤
          data.root digits ^ (-(depth : ℝ)) * Real.exp (slack * depth) := by
  have finite_sum : (∑' depth, (pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound))
      (goodSetPrefixBadAddresses data orderIndex bound depth slack)) ≠ ∞ :=
    ne_top_of_le_ne_top summable.tsum_ofReal_ne_top
      (ENNReal.tsum_le_tsum (goodSetPrefixBadAddresses_mass_bound data orderIndex bound slack))
  filter_upwards [ae_eventually_notMem finite_sum] with digits eventual
  filter_upwards [eventual] with depth not_bad
  apply le_of_not_gt
  intro bad
  apply not_bad
  apply Set.mem_iUnion.mpr
  refine ⟨fun index : Fin depth => digits index, ?_⟩
  exact ⟨fun _ => rfl, bad⟩

/-- The actual conditional cylinder masses satisfy the exponential eventual
bound required by the fixed-parameter Hausdorff argument. -/
theorem goodSetConditional_eventual_prefix_bound_of_summable_tails {exponent : ℝ}
    (data : RootFibreData exponent) (orderIndex bound : ℕ) (slack : ℝ)
    (summable : Summable (goodSetPrefixTailTotal data orderIndex bound slack)) :
    ∀ᵐ parameter ∂(pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound)).map data.root,
      0 < goodSetRootDensity data orderIndex bound parameter ∧
      ∀ᵐ digits ∂goodSetRootConditional data orderIndex bound parameter,
        data.root digits = parameter ∧ ∃ minimumDepth : ℕ, ∀ depth, minimumDepth ≤ depth →
          goodSetRootConditional data orderIndex bound parameter (pairedPrefix digits depth) ≤
            ENNReal.ofReal ((4 * parameter) ^ (-(depth : ℝ)) * Real.exp (slack * depth) /
              goodSetRootDensity data orderIndex bound parameter) := by
  have conditional_eventual :
      ∀ᵐ parameter ∂(pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound)).map data.root,
        ∀ᵐ digits ∂goodSetRootConditional data orderIndex bound parameter,
          ∀ᶠ depth in atTop, goodSetPrefixDensity data orderIndex bound depth
            (fun index : Fin depth => digits index) (data.root digits) ≤
              data.root digits ^ (-(depth : ℝ)) * Real.exp (slack * depth) := by
    apply Measure.ae_ae_of_ae_comp
    rw [show goodSetRootConditional data orderIndex bound =
        condDistrib id data.root (pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound)) from rfl,
      condDistrib_comp_map (rootFibreData_continuous_root data).measurable.aemeasurable aemeasurable_id,
      Measure.map_id]
    exact goodSetPrefixDensity_eventually_of_summable_tails data orderIndex bound slack summable
  filter_upwards [conditional_eventual, goodSetRootConditional_ae_selected_fibre data orderIndex bound,
    goodSetRootDensity_ae_positive data orderIndex bound] with parameter eventual supported positive
  refine ⟨positive, ?_⟩
  filter_upwards [eventual, supported] with digits eventual supported
  refine ⟨supported.2, ?_⟩
  obtain ⟨minimumDepth, after⟩ := eventually_atTop.mp eventual
  refine ⟨minimumDepth, ?_⟩
  intro depth depth_ge
  rw [← finitePairedPrefix_eq_pairedPrefix,
    goodSetConditional_prefix_mass data orderIndex bound depth _ parameter positive]
  apply ENNReal.ofReal_le_ofReal
  have prefix_bound := after depth depth_ge
  rw [supported.2] at prefix_bound
  have scaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left prefix_bound (by positivity : 0 ≤ (4 : ℝ)⁻¹ ^ depth)) positive.le
  have parameter_nonnegative : 0 ≤ parameter := by
    rw [← supported.2]
    linarith [data.lower_gt_quarter, (data.root_in_band digits).1]
  have power_identity : (4 : ℝ)⁻¹ ^ depth * parameter ^ (-(depth : ℝ)) =
      (4 * parameter) ^ (-(depth : ℝ)) := by
    rw [Real.rpow_neg parameter_nonnegative, Real.rpow_natCast,
      Real.rpow_neg (mul_nonneg (by norm_num : 0 ≤ (4 : ℝ)) parameter_nonnegative), Real.rpow_natCast, mul_pow,
      mul_inv_rev, inv_pow]
    ring
  simpa only [← mul_assoc, power_identity] using scaled

end LambdaCantor.First.Roots
