import LambdaCantor.First.RootsGoodSets
import LambdaCantor.First.LinearRegularityMain

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

/-- Actual linear regularity and actual state exceptional-set nullity give
finite positive-order energy at almost every complete source address. -/
theorem rootFibreData_ae_finite_sobolev_energy {exponent : ℝ}
    (data : RootFibreData exponent) :
    ∀ᵐ digits ∂pairedAddressMeasure, ∃ order : ℝ, 0 < order ∧
      projectedSobolevEnergy order (rootFibreState data digits) ≠ ∞ := by
  obtain ⟨exceptional, dimension, regular⟩ :=
    LinearRegularity.projected_law_positive_sobolev_off_exception
  have outside : ∀ᵐ digits ∂pairedAddressMeasure, rootFibreState data digits ∉ exceptional := by
    apply ae_iff.mpr
    simpa only [Set.preimage, not_not] using
      rootFibreData_state_exceptional_null data dimension
  filter_upwards [outside] with digits not_exceptional
  have parameter_band : (rootFibreState data digits).1 ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) := by
    change data.root digits ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)
    exact ⟨data.lower_gt_quarter.trans_le (data.root_in_band digits).1,
      (data.root_in_band digits).2.trans_lt data.upper_lt_half⟩
  obtain ⟨order, positive, integrable⟩ :=
    (regular _ parameter_band _ not_exceptional).2
  refine ⟨order, positive, ?_⟩
  exact ((hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun frequency =>
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)))).1
    integrable.hasFiniteIntegral).ne

/-- A countable family of actual compact good-address sets covers almost
every source address, with one positive order and bound on each member. -/
theorem rootFibreData_ae_compact_good_cover {exponent : ℝ} (data : RootFibreData exponent) :
    (∀ orderIndex bound : ℕ, IsCompact (rootSobolevGoodSet data orderIndex bound)) ∧
      ∀ᵐ digits ∂pairedAddressMeasure,
        digits ∈ ⋃ orderIndex : ℕ, ⋃ bound : ℕ, rootSobolevGoodSet data orderIndex bound := by
  refine ⟨rootFibreData_compact_good_set data, ?_⟩
  filter_upwards [rootFibreData_ae_finite_sobolev_energy data] with digits finite
  obtain ⟨orderIndex, bound, member⟩ := rootFibreData_good_sets_cover_finite_energy data digits finite
  exact Set.mem_iUnion.mpr ⟨orderIndex, Set.mem_iUnion.mpr ⟨bound, member⟩⟩

/-- Once each actual compact good-set restriction has an absolutely continuous
root image, the countable almost-everywhere cover transfers this to the full law.
This is an assembly lemma; the local absolute-continuity premise remains to be proved. -/
theorem rootFibreData_rootLaw_absolutelyContinuous_of_good_sets {exponent : ℝ}
    (data : RootFibreData exponent)
    (local_absolute_continuity : ∀ orderIndex bound : ℕ,
      (pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound)).map data.root ≪ volume) :
    rootLaw data.root ≪ volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro set measurable_set null_set
  have root_measurable := (rootFibreData_continuous_root data).measurable
  have local_avoidance : ∀ orderIndex bound : ℕ,
      ∀ᵐ digits ∂pairedAddressMeasure,
        digits ∈ rootSobolevGoodSet data orderIndex bound → data.root digits ∉ set := by
    intro orderIndex bound
    have null_restriction := local_absolute_continuity orderIndex bound null_set
    rw [Measure.map_apply root_measurable measurable_set,
      Measure.restrict_apply (root_measurable measurable_set)] at null_restriction
    apply ae_iff.mpr
    have bad_set : {digits | ¬ (digits ∈ rootSobolevGoodSet data orderIndex bound →
        data.root digits ∉ set)} = data.root ⁻¹' set ∩ rootSobolevGoodSet data orderIndex bound := by
      ext digits
      simp only [Set.mem_setOf_eq, Classical.not_imp, not_not, Set.mem_inter_iff, Set.mem_preimage]
      exact and_comm
    rw [bad_set]
    exact null_restriction
  have avoidance : ∀ᵐ digits ∂pairedAddressMeasure, data.root digits ∉ set := by
    filter_upwards [(rootFibreData_ae_compact_good_cover data).2,
      ae_all_iff.mpr (fun orderIndex => ae_all_iff.mpr (local_avoidance orderIndex))]
      with digits covered local_avoidance
    obtain ⟨orderIndex, member⟩ := Set.mem_iUnion.mp covered
    obtain ⟨bound, member⟩ := Set.mem_iUnion.mp member
    exact local_avoidance orderIndex bound member
  change pairedAddressMeasure.map data.root set = 0
  rw [Measure.map_apply root_measurable measurable_set]
  simpa only [Set.preimage, not_not] using (ae_iff.mp avoidance)
end LambdaCantor.First.Roots

