import LambdaCantor.AE.DimensionMeasurabilityFiniteSubcover

noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace LambdaCantor.AE

/-- Zero Hausdorff measure of a compact fibre supplies finite open covers with
arbitrarily small positive diameter and total power-cost bounds. -/
theorem exists_finiteOpenCover_of_hausdorffMeasure_zero
    {fibre : Set (ℝ × ℝ)} (compact : IsCompact fibre)
    {dimension : ℝ} (dimension_positive : 0 < dimension)
    (zero_measure : Measure.hausdorffMeasure dimension fibre = 0)
    (scale : ℝ≥0) (scale_positive : 0 < scale) :
    ∃ certificate : FiniteOpenCoverCertificate dimension (scale : ℝ≥0∞),
      fibre ⊆ ⋃ index, certificate.sets index := by
  classical
  have half_positive : (0 : ℝ≥0∞) < ((scale/2 : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast (half_pos scale_positive)
  have half_lt : ((scale/2 : ℝ≥0) : ℝ≥0∞) < (scale : ℝ≥0∞) := by
    exact_mod_cast (half_lt_self scale_positive)
  obtain ⟨sets, covered, diameters, original_cost⟩ :=
    exists_small_countable_cover_of_hausdorffMeasure_zero zero_measure half_positive half_positive
  have remove_empty : ∀ index, (⨆ _ : (sets index).Nonempty,
      Metric.ediam (sets index) ^ dimension) = Metric.ediam (sets index) ^ dimension := by
    intro index
    by_cases nonempty : (sets index).Nonempty
    · simp [nonempty]
    · rw [Set.not_nonempty_iff_eq_empty.mp nonempty]
      simp [ENNReal.zero_rpow_of_pos dimension_positive]
  simp_rw [remove_empty] at original_cost
  obtain ⟨slack, slack_positive, slack_sum⟩ :=
    ENNReal.exists_pos_sum_of_countable' half_positive.ne' ℕ
  have each_cost_finite : ∀ index, Metric.ediam (sets index) ^ dimension ≠ ⊤ := by
    intro index
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top
      ((ENNReal.le_tsum index).trans original_cost.le)
  obtain ⟨openSets, open_sets, contains, open_diameters, open_cost⟩ :=
    exists_countable_open_enlargement sets dimension_positive
      (fun index => (diameters index).trans_lt half_lt)
      (fun index => Metric.ediam (sets index) ^ dimension + slack index)
      (fun index => ENNReal.lt_add_right (each_cost_finite index) (slack_positive index).ne')
  have total_cost : (∑' index, Metric.ediam (openSets index) ^ dimension) ≤ (scale : ℝ≥0∞) := by
    apply open_cost.trans
    rw [ENNReal.tsum_add]
    have summed := ENNReal.add_lt_add original_cost slack_sum
    have halves : ((scale/2 : ℝ≥0) : ℝ≥0∞) + ((scale/2 : ℝ≥0) : ℝ≥0∞) = (scale : ℝ≥0∞) := by
      rw [← ENNReal.coe_add, add_halves]
    exact (summed.trans_eq halves).le
  have open_covered : fibre ⊆ ⋃ index, openSets index :=
    covered.trans (iUnion_mono contains)
  obtain ⟨indices, finite_covered, finite_cost⟩ :=
    exists_finite_open_subcover_with_cost compact openSets open_sets open_covered dimension total_cost
  let enumeration := (Fintype.equivFin ↥indices).symm
  refine ⟨{
    length := Fintype.card ↥indices
    sets := fun index => openSets (enumeration index).val
    isOpen_sets := fun index => open_sets _
    diameter_bound := fun index => (open_diameters _).le
    cost_bound := ?_
  }, ?_⟩
  · have reindex := Equiv.sum_comp enumeration
      (fun index : ↥indices => Metric.ediam (openSets index.val) ^ dimension)
    rw [reindex]
    rw [← Finset.sum_subtype indices (fun _ => Iff.rfl)
      (fun index : ℕ => Metric.ediam (openSets index) ^ dimension)]
    exact finite_cost
  · intro point point_mem
    obtain ⟨index, index_mem, spatial_mem⟩ := mem_iUnion₂.mp (finite_covered point_mem)
    exact mem_iUnion.mpr ⟨enumeration.symm ⟨index, index_mem⟩, by simpa using spatial_mem⟩

end LambdaCantor.AE
