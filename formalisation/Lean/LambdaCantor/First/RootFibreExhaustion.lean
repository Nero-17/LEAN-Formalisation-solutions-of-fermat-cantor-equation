import LambdaCantor.First.RootsGoodSetExhaustion

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace LambdaCantor.First.Roots

/-- Countable good-set exhaustion dominates the full root law as measures.
The good sets may overlap; disjointness is not required for this inequality. -/
theorem rootFibreData_rootLaw_le_sum_good_sets {exponent : ℝ}
    (data : RootFibreData exponent) :
    rootLaw data.root ≤ Measure.sum (fun indices : ℕ × ℕ =>
      (pairedAddressMeasure.restrict
        (rootSobolevGoodSet data indices.1 indices.2)).map data.root) := by
  let selected : ℕ × ℕ → Set (ℕ → Bool × Bool) :=
    fun indices => rootSobolevGoodSet data indices.1 indices.2
  have covered : ∀ᵐ digits ∂pairedAddressMeasure, digits ∈ ⋃ indices, selected indices := by
    filter_upwards [(rootFibreData_ae_compact_good_cover data).2] with digits member
    obtain ⟨orderIndex, member⟩ := Set.mem_iUnion.mp member
    obtain ⟨bound, member⟩ := Set.mem_iUnion.mp member
    exact Set.mem_iUnion.mpr ⟨(orderIndex, bound), member⟩
  have dominated : pairedAddressMeasure ≤
      Measure.sum (fun indices => pairedAddressMeasure.restrict (selected indices)) := by
    have bound := Measure.restrict_iUnion_le (μ := pairedAddressMeasure) (s := selected)
    rw [Measure.restrict_eq_self_of_ae_mem covered] at bound
    exact bound
  have pushed := Measure.map_mono dominated (rootFibreData_continuous_root data).measurable
  rw [Measure.map_sum (rootFibreData_continuous_root data).measurable.aemeasurable] at pushed
  exact pushed

/-- Nullity transfers from all restricted root laws for an arbitrary target
set, without imposing measurability on a Hausdorff-dimension failure set. -/
theorem rootFibreData_rootLaw_null_of_good_sets {exponent : ℝ}
    (data : RootFibreData exponent) (target : Set ℝ)
    (local_null : ∀ orderIndex bound : ℕ,
      (pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound)).map
        data.root target = 0) :
    rootLaw data.root target = 0 := by
  apply le_antisymm _ zero_le
  calc
    rootLaw data.root target ≤
        Measure.sum (fun indices : ℕ × ℕ =>
          (pairedAddressMeasure.restrict
            (rootSobolevGoodSet data indices.1 indices.2)).map data.root) target :=
      Measure.le_iff'.mp (rootFibreData_rootLaw_le_sum_good_sets data) target
    _ = 0 := by
      rw [Measure.sum_apply_of_countable]
      simp only [local_null, tsum_zero]

theorem rootFibreData_rootLaw_ae_of_good_sets {exponent : ℝ}
    (data : RootFibreData exponent) (predicate : ℝ → Prop)
    (local_property : ∀ orderIndex bound : ℕ,
      ∀ᵐ ratio ∂(pairedAddressMeasure.restrict
        (rootSobolevGoodSet data orderIndex bound)).map data.root, predicate ratio) :
    ∀ᵐ ratio ∂rootLaw data.root, predicate ratio := by
  apply ae_iff.mpr
  apply rootFibreData_rootLaw_null_of_good_sets data
  intro orderIndex bound
  exact ae_iff.mp (local_property orderIndex bound)

end LambdaCantor.First.Roots
