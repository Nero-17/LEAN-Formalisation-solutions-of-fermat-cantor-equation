import LambdaCantor.SelfSimilarity

noncomputable section
namespace LambdaCantor.Last

theorem low_copy_mem {ratio coordinate : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (membership : coordinate ∈ cantorSet ratio) :
    ratio*coordinate ∈ cantorSet ratio := by
  rw [cantorSet_selfsimilar nonnegative less_one]
  exact Or.inl ⟨coordinate, membership, rfl⟩

theorem high_copy_mem {ratio coordinate : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (membership : coordinate ∈ cantorSet ratio) :
    1-ratio+ratio*coordinate ∈ cantorSet ratio := by
  rw [cantorSet_selfsimilar nonnegative less_one]
  exact Or.inr ⟨coordinate, membership, rfl⟩

/-- A gap longer than the central gap must be wholly inside a single copy.
Its inverse affine image is again an empty interval with Cantor endpoints. -/
theorem oversized_gap_rescale {ratio left right : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2)
    (left_mem : left ∈ cantorSet ratio) (right_mem : right ∈ cantorSet ratio)
    (oversized : 1-2*ratio < right-left)
    (empty_interval : ∀ coordinate ∈ cantorSet ratio, coordinate ∉ Set.Ioo left right) :
    ∃ first ∈ cantorSet ratio, ∃ second ∈ cantorSet ratio,
      right-left = ratio*(second-first) ∧
      1-2*ratio < second-first ∧
      ∀ coordinate ∈ cantorSet ratio, coordinate ∉ Set.Ioo first second := by
  have less_one : ratio < 1 := by linarith
  have left_bound := cantorSet_subset_unitInterval positive.le less_one left_mem
  have right_bound := cantorSet_subset_unitInterval positive.le less_one right_mem
  have left_split := left_mem
  have right_split := right_mem
  rw [cantorSet_selfsimilar positive.le less_one] at left_split right_split
  rcases left_split with ⟨first, first_mem, rfl⟩ | ⟨first, first_mem, rfl⟩ <;>
    rcases right_split with ⟨second, second_mem, rfl⟩ | ⟨second, second_mem, rfl⟩
  · refine ⟨first, first_mem, second, second_mem, by ring, ?_, ?_⟩
    · by_contra failure
      have bound := mul_le_mul_of_nonneg_left (le_of_not_gt failure) positive.le
      nlinarith [mul_pos (show 0 < 1-ratio by linarith) (show 0 < 1-2*ratio by linarith)]
    · intro coordinate membership inside
      apply empty_interval (ratio*coordinate) (low_copy_mem positive.le less_one membership)
      exact ⟨mul_lt_mul_of_pos_left inside.1 positive,
        mul_lt_mul_of_pos_left inside.2 positive⟩
  · have first_bounds := cantorSet_subset_unitInterval positive.le less_one first_mem
    have second_bounds := cantorSet_subset_unitInterval positive.le less_one second_mem
    have lower_edge_mem : ratio ∈ cantorSet ratio := by
      simpa using low_copy_mem positive.le less_one (one_mem_cantorSet positive.le less_one)
    have upper_edge_mem : 1-ratio ∈ cantorSet ratio := by
      simpa using high_copy_mem positive.le less_one (zero_mem_cantorSet ratio)
    have left_at_edge : ratio*first = ratio := by
      have upper := mul_le_mul_of_nonneg_left first_bounds.2 positive.le
      by_contra unequal
      have strict : ratio*first < ratio := lt_of_le_of_ne (by nlinarith) unequal
      apply empty_interval ratio lower_edge_mem
      constructor <;> nlinarith [mul_nonneg positive.le second_bounds.1]
    have right_at_edge : 1-ratio+ratio*second = 1-ratio := by
      have lower := mul_nonneg positive.le second_bounds.1
      by_contra unequal
      have strict : 1-ratio < 1-ratio+ratio*second :=
        lt_of_le_of_ne (by linarith) (Ne.symm unequal)
      apply empty_interval (1-ratio) upper_edge_mem
      constructor <;> nlinarith
    exfalso
    linarith
  · have first_bounds := cantorSet_subset_unitInterval positive.le less_one first_mem
    have second_bounds := cantorSet_subset_unitInterval positive.le less_one second_mem
    exfalso
    nlinarith [mul_nonneg positive.le first_bounds.1,
      mul_le_mul_of_nonneg_left second_bounds.2 positive.le]
  · refine ⟨first, first_mem, second, second_mem, by ring, ?_, ?_⟩
    · by_contra failure
      have bound := mul_le_mul_of_nonneg_left (le_of_not_gt failure) positive.le
      nlinarith [mul_pos (show 0 < 1-ratio by linarith) (show 0 < 1-2*ratio by linarith)]
    · intro coordinate membership inside
      apply empty_interval (1-ratio+ratio*coordinate) (high_copy_mem positive.le less_one membership)
      constructor <;> nlinarith [mul_lt_mul_of_pos_left inside.1 positive,
        mul_lt_mul_of_pos_left inside.2 positive]

theorem cantor_gap_length_le {ratio left right : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2)
    (left_mem : left ∈ cantorSet ratio) (right_mem : right ∈ cantorSet ratio)
    (empty_interval : ∀ coordinate ∈ cantorSet ratio, coordinate ∉ Set.Ioo left right) :
    right-left ≤ 1-2*ratio := by
  have less_one : ratio < 1 := by linarith
  have iterative_bound : ∀ depth : ℕ, ∀ first ∈ cantorSet ratio, ∀ second ∈ cantorSet ratio,
      1-2*ratio < second-first →
      (∀ coordinate ∈ cantorSet ratio, coordinate ∉ Set.Ioo first second) →
      second-first ≤ ratio^depth := by
    intro depth
    induction depth with
    | zero =>
      intro first first_mem second second_mem oversized empty
      have first_bounds := cantorSet_subset_unitInterval positive.le less_one first_mem
      have second_bounds := cantorSet_subset_unitInterval positive.le less_one second_mem
      simpa using (show second-first ≤ 1 by linarith [first_bounds.1, second_bounds.2])
    | succ depth induction =>
      intro first first_mem second second_mem oversized empty
      obtain ⟨next_first, next_first_mem, next_second, next_second_mem, length_eq,
        next_oversized, next_empty⟩ :=
        oversized_gap_rescale positive less_half first_mem second_mem oversized empty
      rw [length_eq, pow_succ]
      have bound := induction next_first next_first_mem next_second next_second_mem next_oversized next_empty
      nlinarith [mul_le_mul_of_nonneg_left bound positive.le]
  by_contra failure
  have oversized : 1-2*ratio < right-left := lt_of_not_ge failure
  have width_positive : 0 < right-left := by linarith
  obtain ⟨depth, small⟩ := exists_pow_lt_of_lt_one width_positive less_one
  exact (not_lt_of_ge (iterative_bound depth left left_mem right right_mem oversized empty_interval)) small

end LambdaCantor.Last



