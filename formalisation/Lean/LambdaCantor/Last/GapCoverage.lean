import LambdaCantor.Last.ScalarCylinders

noncomputable section
namespace LambdaCantor.Last

theorem approximable_of_avoids_central_gaps {ratio coordinate : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2)
    (bounds : coordinate ∈ Set.Icc (0 : ℝ) 1)
    (avoids : ∀ word : List Bool,
      coordinate ∉ scalarWordMap ratio word '' Set.Ioo ratio (1-ratio))
    (depth : ℕ) : ∃ point ∈ cantorSet ratio, |coordinate-point| ≤ ratio^depth := by
  have less_one : ratio < 1 := by linarith
  induction depth generalizing coordinate with
  | zero =>
    refine ⟨0, zero_mem_cantorSet ratio, ?_⟩
    simpa [abs_of_nonneg bounds.1] using bounds.2
  | succ depth induction =>
    by_cases lower_branch : coordinate ≤ ratio
    · have tail_bounds : coordinate/ratio ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg bounds.1 positive.le
        · exact (div_le_one positive).mpr lower_branch
      have tail_avoids : ∀ word : List Bool,
          coordinate/ratio ∉ scalarWordMap ratio word '' Set.Ioo ratio (1-ratio) := by
        rintro word ⟨gap_coordinate, in_gap, equation⟩
        apply avoids (false::word)
        refine ⟨gap_coordinate, in_gap, ?_⟩
        simp only [scalarWordMap, Bool.false_eq_true, if_false, zero_add, equation]
        exact mul_div_cancel₀ coordinate positive.ne'
      obtain ⟨point, point_mem, close⟩ := induction tail_bounds tail_avoids
      refine ⟨ratio*point, low_copy_mem positive.le less_one point_mem, ?_⟩
      have coordinate_identity : coordinate-ratio*point = ratio*(coordinate/ratio-point) := by
        rw [mul_sub, mul_div_cancel₀ _ positive.ne']
      rw [coordinate_identity, abs_mul, abs_of_pos positive, pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left close positive.le]
    · have upper_branch : 1-ratio ≤ coordinate := by
        by_contra failure
        apply avoids []
        exact ⟨coordinate, ⟨lt_of_not_ge lower_branch, lt_of_not_ge failure⟩, rfl⟩
      have tail_bounds : (coordinate-(1-ratio))/ratio ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg (sub_nonneg.mpr upper_branch) positive.le
        · apply (div_le_one positive).mpr
          linarith [bounds.2]
      have tail_avoids : ∀ word : List Bool,
          (coordinate-(1-ratio))/ratio ∉ scalarWordMap ratio word '' Set.Ioo ratio (1-ratio) := by
        rintro word ⟨gap_coordinate, in_gap, equation⟩
        apply avoids (true::word)
        refine ⟨gap_coordinate, in_gap, ?_⟩
        simp only [scalarWordMap, if_true, equation, mul_div_cancel₀ _ positive.ne']
        ring
      obtain ⟨point, point_mem, close⟩ := induction tail_bounds tail_avoids
      refine ⟨1-ratio+ratio*point, high_copy_mem positive.le less_one point_mem, ?_⟩
      have coordinate_identity : coordinate-(1-ratio+ratio*point) =
          ratio*((coordinate-(1-ratio))/ratio-point) := by
        rw [mul_sub, mul_div_cancel₀ _ positive.ne']
        ring
      rw [coordinate_identity, abs_mul, abs_of_pos positive, pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left close positive.le]

theorem mem_cantorSet_of_avoids_central_gaps {ratio coordinate : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2)
    (bounds : coordinate ∈ Set.Icc (0 : ℝ) 1)
    (avoids : ∀ word : List Bool,
      coordinate ∉ scalarWordMap ratio word '' Set.Ioo ratio (1-ratio)) :
    coordinate ∈ cantorSet ratio := by
  have closed := (isCompact_cantorSet positive.le (show ratio < 1 by linarith)).isClosed
  rw [← closed.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro epsilon epsilon_positive
  obtain ⟨depth, small⟩ := exists_pow_lt_of_lt_one epsilon_positive (show ratio < 1 by linarith)
  obtain ⟨point, point_mem, close⟩ := approximable_of_avoids_central_gaps positive less_half bounds avoids depth
  exact ⟨point, point_mem, by simpa [Real.dist_eq] using close.trans_lt small⟩

theorem central_gaps_cover_complement {ratio : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2) :
    Set.Icc (0 : ℝ) 1 \ cantorSet ratio =
      ⋃ word : List Bool, scalarWordMap ratio word '' Set.Ioo ratio (1-ratio) := by
  ext coordinate
  constructor
  · rintro ⟨bounds, outside⟩
    by_contra not_in_union
    apply outside
    apply mem_cantorSet_of_avoids_central_gaps positive less_half bounds
    intro word membership
    exact not_in_union (Set.mem_iUnion.mpr ⟨word, membership⟩)
  · intro membership
    rcases Set.mem_iUnion.mp membership with ⟨word, gap_coordinate, in_gap, rfl⟩
    constructor
    · apply scalarWordMap_bounds positive.le (by linarith) word
      constructor <;> linarith [in_gap.1, in_gap.2]
    · exact Set.disjoint_left.mp (scalar_central_gap_disjoint positive less_half word)
        ⟨gap_coordinate, in_gap, rfl⟩

end LambdaCantor.Last
