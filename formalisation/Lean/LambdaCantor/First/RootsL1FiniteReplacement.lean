import LambdaCantor.First.RootsL1Linearity

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

/-- Exact finite-measure density linearity turns uniform branch replacement
estimates into an estimate weighted by the original cylinder masses. -/
theorem finite_density_replacement_bound {Index : Type*} (indices : Finset Index)
    (first second : Index → Measure ℝ)
    (first_exists : ∀ index, LinearRegularity.HasL2Density (first index))
    (second_exists : ∀ index, LinearRegularity.HasL2Density (second index))
    (weights : Index → ℝ≥0∞) (finite_weights : ∀ index, weights index ≠ ∞)
    (error : ℝ)
    (replacement : ∀ index ∈ indices,
      ‖measureDensityL1 (first index) (first_exists index) -
        measureDensityL1 (second index) (second_exists index)‖ ≤ error) :
    ‖measureDensityL1 (∑ index ∈ indices, weights index • first index)
        (hasL2Density_finset_sum indices _ (fun index _ =>
          hasL2Density_smul (first_exists index) (weights index) (finite_weights index))) -
      measureDensityL1 (∑ index ∈ indices, weights index • second index)
        (hasL2Density_finset_sum indices _ (fun index _ =>
          hasL2Density_smul (second_exists index) (weights index) (finite_weights index)))‖ ≤
      (∑ index ∈ indices, (weights index).toReal) * error := by
  have weighted_linearity (measures : Index → Measure ℝ)
      (density_exists : ∀ index, LinearRegularity.HasL2Density (measures index)) :
      measureDensityL1 (∑ index ∈ indices, weights index • measures index)
        (hasL2Density_finset_sum indices _ (fun index _ =>
          hasL2Density_smul (density_exists index) (weights index) (finite_weights index))) =
        ∑ index ∈ indices, (weights index).toReal • measureDensityL1 (measures index) (density_exists index) := by
    refine (measureDensityL1_finset_sum indices _ (fun index =>
      hasL2Density_smul (density_exists index) (weights index) (finite_weights index))).trans ?_
    apply Finset.sum_congr rfl
    intro index member
    exact measureDensityL1_smul (density_exists index) (weights index) (finite_weights index)
  rw [weighted_linearity first first_exists, weighted_linearity second second_exists]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ index ∈ indices,
        ‖(weights index).toReal • measureDensityL1 (first index) (first_exists index) -
          (weights index).toReal • measureDensityL1 (second index) (second_exists index)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ index ∈ indices, (weights index).toReal * error := by
      apply Finset.sum_le_sum
      intro index member
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_mul_of_nonneg_left (replacement index member) ENNReal.toReal_nonneg
    _ = _ := (Finset.sum_mul _ _ _).symm

end LambdaCantor.First.Roots
