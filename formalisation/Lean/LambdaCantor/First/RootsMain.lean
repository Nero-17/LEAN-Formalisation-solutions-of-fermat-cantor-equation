import LambdaCantor.First.RootsAbsoluteContinuity
import LambdaCantor.First.RootsPrefixEnvelope
import LambdaCantor.First.RootsConditionalDimension
import LambdaCantor.First.RootFibreExhaustion
import LambdaCantor.First.RootFibreConsequences
import LambdaCantor.First.Upper

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
namespace LambdaCantor.First.Roots

/-- The logarithmic conditional exponent is the manuscript's dimension. -/
theorem conditional_dimension_exponent_eq_expected {ratio : ℝ}
    (positive : 0 < ratio) (less_one : ratio < 1) :
    Real.log (4 * ratio) / Real.log (1 / ratio) = expectedDimension ratio := by
  have logarithm_positive : 0 < Real.log (1 / ratio) :=
    Real.log_pos ((one_lt_div positive).mpr less_one)
  have reciprocal_log : Real.log (1 / ratio) = -Real.log ratio := by
    rw [one_div, Real.log_inv]
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) positive.ne', First.log_four]
  unfold expectedDimension
  field_simp [logarithm_positive.ne']
  nlinarith [reciprocal_log]

/-- The conditional dimension theorem on each genuine compact good set.
Only a countable sequence of losses is intersected in parameter space. -/
theorem rootSobolevGoodSet_ae_dimension {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound : ℕ) :
    ∀ᵐ parameter ∂(pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound)).map data.root,
      dimH (intersection exponent parameter) = ENNReal.ofReal (expectedDimension parameter) := by
  have all_rates : ∀ᵐ parameter ∂(pairedAddressMeasure.restrict
      (rootSobolevGoodSet data orderIndex bound)).map data.root,
      ∀ lossIndex : ℕ, 0 < goodSetRootDensity data orderIndex bound parameter ∧
        ∀ᵐ digits ∂goodSetRootConditional data orderIndex bound parameter,
          data.root digits = parameter ∧ ∃ minimumDepth : ℕ, ∀ depth, minimumDepth ≤ depth →
            goodSetRootConditional data orderIndex bound parameter (pairedPrefix digits depth) ≤
              ENNReal.ofReal ((4 * parameter) ^ (-(depth : ℝ)) *
                Real.exp ((1 / ((lossIndex : ℝ) + 1)) * depth) /
                  goodSetRootDensity data orderIndex bound parameter) := by
    apply ae_all_iff.mpr
    intro lossIndex
    exact goodSetConditional_eventual_prefix_bound_of_summable_tails data orderIndex bound
      (1 / ((lossIndex : ℝ) + 1))
      (rootSobolevGoodSet_prefix_tails_summable data orderIndex bound _ (by positivity))
  filter_upwards [all_rates, goodSetRootConditional_ae_selected_fibre data orderIndex bound]
    with parameter rates supported
  have fibre : ∀ᵐ digits ∂goodSetRootConditional data orderIndex bound parameter,
      data.root digits = parameter := supported.mono (fun _ property => property.2)
  obtain ⟨digits, root_eq⟩ := fibre.exists
  have parameter_band : parameter ∈ Set.Icc data.lower data.upper := by
    rw [← root_eq]
    exact data.root_in_band digits
  have parameter_positive : 0 < parameter := by linarith [data.lower_gt_quarter, parameter_band.1]
  have parameter_less_one : parameter < 1 := by linarith [data.upper_lt_half, parameter_band.2]
  have lower := conditional_dimension_lower_of_arbitrarily_small_loss data
    (goodSetRootConditional data orderIndex bound parameter) fibre
    (show ∀ loss : ℝ, 0 < loss → ∃ normalizer : ℝ, 0 < normalizer ∧
      ∀ᵐ address ∂goodSetRootConditional data orderIndex bound parameter,
        ∃ minimumDepth : ℕ, ∀ depth ≥ minimumDepth,
          goodSetRootConditional data orderIndex bound parameter (pairedPrefix address depth) ≤
            ENNReal.ofReal ((4 * parameter) ^ (-(depth : ℝ)) * Real.exp (loss * depth) / normalizer) by
      intro loss positive_loss
      obtain ⟨lossIndex, smaller⟩ := exists_nat_one_div_lt positive_loss
      refine ⟨goodSetRootDensity data orderIndex bound parameter, (rates lossIndex).1, ?_⟩
      filter_upwards [(rates lossIndex).2] with address property
      obtain ⟨minimumDepth, after⟩ := property.2
      refine ⟨minimumDepth, ?_⟩
      intro depth depth_ge
      apply (after depth depth_ge).trans
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ (rates lossIndex).1.le
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right smaller.le (Nat.cast_nonneg depth))
  rw [conditional_dimension_exponent_eq_expected parameter_positive parameter_less_one] at lower
  apply le_antisymm _ lower
  have upper := First.dimension_upper data.exponent_gt_one parameter_positive
    (show parameter ≤ 1 / 2 by linarith [data.upper_lt_half, parameter_band.2])
  have expected_positive := expectedDimension_positive
    (data.lower_gt_quarter.trans_le parameter_band.1)
    (parameter_band.2.trans_lt data.upper_lt_half)
  change dimH (intersection exponent parameter) ≤
    ENNReal.ofReal (max (expectedDimension parameter) 0) at upper
  simpa only [max_eq_left expected_positive.le] using upper

/-- Manuscript Lemma root-fibres, from its concrete geometric hypotheses.
All compact-set density, conditional dimension and exhaustion premises are
discharged by the internal constructions above. -/
theorem root_fibres {exponent : ℝ} (data : RootFibreData exponent) : RootFibreConclusion data := by
  refine ⟨rootFibreData_rootLaw_absolutelyContinuous data, ?_⟩
  exact rootFibreData_rootLaw_ae_of_good_sets data _ (rootSobolevGoodSet_ae_dimension data)

end LambdaCantor.First.Roots
