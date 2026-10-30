import LambdaCantor.AE.DimensionMeasurabilityEnlargement

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LambdaCantor.AE

/-- Passing to a finite subcover cannot increase the nonnegative power cost. -/
theorem exists_finite_open_subcover_with_cost {fibre : Set (ℝ × ℝ)}
    (compact : IsCompact fibre) (sets : ℕ → Set (ℝ × ℝ))
    (open_sets : ∀ index, IsOpen (sets index)) (covered : fibre ⊆ ⋃ index, sets index)
    (dimension : ℝ) {budget : ℝ≥0∞}
    (cost_bound : (∑' index, Metric.ediam (sets index) ^ dimension) ≤ budget) :
    ∃ indices : Finset ℕ, fibre ⊆ (⋃ index ∈ indices, sets index) ∧
      (∑ index ∈ indices, Metric.ediam (sets index) ^ dimension) ≤ budget := by
  obtain ⟨indices, finite_covered⟩ := compact.elim_finite_subcover sets open_sets covered
  exact ⟨indices, finite_covered, (ENNReal.sum_le_tsum indices).trans cost_bound⟩

/-- Enlargement of a countable cover with explicitly allocated summable cost
slack. The budgets are numerical inputs; no topological conclusion is assumed. -/
theorem exists_countable_open_enlargement
    (sets : ℕ → Set (ℝ × ℝ)) {dimension : ℝ} (dimension_positive : 0 < dimension)
    {scale : ℝ≥0∞} (diameter_lt : ∀ index, Metric.ediam (sets index) < scale)
    (budgets : ℕ → ℝ≥0∞)
    (cost_lt : ∀ index, Metric.ediam (sets index) ^ dimension < budgets index) :
    ∃ openSets : ℕ → Set (ℝ × ℝ),
      (∀ index, IsOpen (openSets index)) ∧
      (∀ index, sets index ⊆ openSets index) ∧
      (∀ index, Metric.ediam (openSets index) < scale) ∧
      (∑' index, Metric.ediam (openSets index) ^ dimension) ≤ ∑' index, budgets index := by
  classical
  choose openSets open_sets contains diameters costs using
    (fun index => exists_open_enlargement dimension_positive.le (diameter_lt index) (cost_lt index))
  exact ⟨openSets, open_sets, contains, diameters, ENNReal.tsum_le_tsum fun index => (costs index).le⟩

end LambdaCantor.AE

