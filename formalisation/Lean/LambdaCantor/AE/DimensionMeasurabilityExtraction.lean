import LambdaCantor.AE.DimensionMeasurabilityOpenCovers

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal
namespace LambdaCantor.AE

/-- Extract a genuinely small countable cover from the library definition of
zero Hausdorff measure. Empty sets contribute zero, as in that definition. -/
theorem exists_small_countable_cover_of_hausdorffMeasure_zero
    {dimension : ℝ} {fibre : Set (ℝ × ℝ)}
    (zero_measure : Measure.hausdorffMeasure dimension fibre = 0)
    {scale budget : ℝ≥0∞} (scale_positive : 0 < scale) (budget_positive : 0 < budget) :
    ∃ sets : ℕ → Set (ℝ × ℝ),
      fibre ⊆ (⋃ index, sets index) ∧
      (∀ index, Metric.ediam (sets index) ≤ scale) ∧
      (∑' index, ⨆ _ : (sets index).Nonempty, Metric.ediam (sets index) ^ dimension) < budget := by
  have content_bound :
      (⨅ (sets : ℕ → Set (ℝ × ℝ)) (_ : fibre ⊆ ⋃ index, sets index)
        (_ : ∀ index, Metric.ediam (sets index) ≤ scale),
        ∑' index, ⨆ _ : (sets index).Nonempty, Metric.ediam (sets index) ^ dimension) ≤
      Measure.hausdorffMeasure dimension fibre := by
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup_of_le scale (le_iSup_of_le scale_positive le_rfl)
  rw [zero_measure] at content_bound
  have content_small := content_bound.trans_lt budget_positive
  simpa only [iInf_lt_iff, exists_prop] using content_small

end LambdaCantor.AE



