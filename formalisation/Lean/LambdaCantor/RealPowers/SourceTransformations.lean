import LambdaCantor.Last.ReturnWords

noncomputable section
namespace LambdaCantor.RealPowers
open Last

-- Generic fibre transformation from Last.SourceSwap.
/-- Swapping the two coordinates preserves positive dimension of a dust fibre. -/
theorem positive_dimension_of_swapped_source {function : (ℝ × ℝ) → ℝ} {ratio level : ℝ}
    (positive : 0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧ function point.swap = level}) :
    0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧ function point = level} := by
  have swap_isometry : Isometry (Prod.swap : ℝ × ℝ → ℝ × ℝ) := by
    apply Isometry.of_dist_eq
    intro first second
    simp only [Prod.dist_eq, Prod.fst_swap, Prod.snd_swap, max_comm]
  apply positive.trans_le (swap_isometry.antilipschitz.le_dimH_image _ |>.trans (dimH_mono ?_))
  rintro point ⟨source, source_mem, rfl⟩
  exact ⟨⟨source_mem.1.2, source_mem.1.1⟩, source_mem.2⟩

-- Generic zero-fibre normalization from Last.SourceNormalization.
theorem positive_dimension_of_source_div {function : (ℝ × ℝ) → ℝ} {ratio height : ℝ}
    (height_nonzero : height ≠ 0)
    (positive : 0 < dimH {point | point ∈ cantorDust ratio ∧ function point/height = 0}) :
    0 < dimH {point | point ∈ cantorDust ratio ∧ function point = 0} := by
  simpa only [div_eq_zero_iff, height_nonzero, or_false] using positive


end LambdaCantor.RealPowers
