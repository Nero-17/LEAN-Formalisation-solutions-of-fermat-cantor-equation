import LambdaCantor.SelfSimilarity
import LambdaCantor.Classical.Source

noncomputable section
namespace LambdaCantor.Classical

def replaceTail (digits : ℕ → Bool) (depth : ℕ) (tail : ℕ → Bool) : ℕ → Bool :=
  fun j => if j < depth then digits j else tail (j - depth)

theorem address_replaceTail (digits tail : ℕ → Bool) (depth : ℕ) :
    address (1 / 3) (replaceTail digits depth tail) =
      prefixValue (1 / 3) digits depth + (1 / 3 : ℝ) ^ depth * address (1 / 3) tail := by
  rw [address_prefix_tail (by norm_num) (by norm_num) (replaceTail digits depth tail) depth]
  have prefix_eq : prefixValue (1 / 3) (replaceTail digits depth tail) depth =
      prefixValue (1 / 3) digits depth := by
    unfold prefixValue
    congr 1
    apply Finset.sum_congr rfl
    intro j membership
    simp [replaceTail, Finset.mem_range.mp membership]
  have tail_equality : (fun j => replaceTail digits depth tail (j + depth)) = tail := by
    funext j
    simp [replaceTail]
  rw [prefix_eq, tail_equality]

theorem prefix_cantor_embedding (digits : ℕ → Bool) (depth : ℕ)
    {tail : ℝ} (membership : tail ∈ cantorSet (1 / 3)) :
    prefixValue (1 / 3) digits depth + (1 / 3 : ℝ) ^ depth * tail ∈ cantorSet (1 / 3) := by
  obtain ⟨tailDigits, rfl⟩ := membership
  exact ⟨replaceTail digits depth tailDigits, address_replaceTail digits tailDigits depth⟩

theorem prefix_square_bounds (digits : ℕ → Bool) (depth : ℕ) :
    0 ≤ prefixValue (1 / 3) digits depth ∧
      prefixValue (1 / 3) digits depth + (1 / 3 : ℝ) ^ depth ≤ 1 := by
  have left_member := prefix_cantor_embedding digits depth (zero_mem_cantorSet (1 / 3))
  have right_member := prefix_cantor_embedding digits depth
    (one_mem_cantorSet (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num))
  have left_bound := LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) left_member
  have right_bound := LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) right_member
  simpa using And.intro left_bound.1 right_bound.2

theorem unit_square_affine_distance (u v side first second originalFirst originalSecond : ℝ)
    (side_nonnegative : 0 ≤ side)
    (first_bounds : first ∈ Set.Icc (0 : ℝ) 1)
    (second_bounds : second ∈ Set.Icc (0 : ℝ) 1)
    (original_first_bounds : originalFirst ∈ Set.Icc (0 : ℝ) 1)
    (original_second_bounds : originalSecond ∈ Set.Icc (0 : ℝ) 1) :
    dist (u + side * first, v + side * second)
      (u + side * originalFirst, v + side * originalSecond) ≤ side := by
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq]
  constructor
  · rw [abs_le]
    constructor <;> nlinarith [mul_nonneg side_nonnegative first_bounds.1,
      mul_nonneg side_nonnegative original_first_bounds.1,
      mul_le_mul_of_nonneg_left first_bounds.2 side_nonnegative,
      mul_le_mul_of_nonneg_left original_first_bounds.2 side_nonnegative]
  · rw [abs_le]
    constructor <;> nlinarith [mul_nonneg side_nonnegative second_bounds.1,
      mul_nonneg side_nonnegative original_second_bounds.1,
      mul_le_mul_of_nonneg_left second_bounds.2 side_nonnegative,
      mul_le_mul_of_nonneg_left original_second_bounds.2 side_nonnegative]

theorem cylinder_eventually_in_ball (first second : ℕ → Bool) (radius : ℝ)
    (radius_positive : 0 < radius) :
    ∃ start, ∀ depth ≥ start, ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      dist (prefixValue (1 / 3) first depth + (1 / 3 : ℝ) ^ depth * a,
        prefixValue (1 / 3) second depth + (1 / 3 : ℝ) ^ depth * b)
        (address (1 / 3) first, address (1 / 3) second) < radius := by
  have vanishing : Filter.Tendsto (fun depth : ℕ => (1 / 3 : ℝ) ^ depth)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  have eventually_small := (tendsto_order.mp vanishing).2 radius radius_positive
  obtain ⟨start, bound⟩ := Filter.eventually_atTop.mp eventually_small
  refine ⟨start, fun depth depth_large a b a_bounds b_bounds => ?_⟩
  rw [address_prefix_tail (by norm_num) (by norm_num) first depth,
    address_prefix_tail (by norm_num) (by norm_num) second depth]
  apply lt_of_le_of_lt (unit_square_affine_distance _ _ _ _ _ _ _ (by positivity)
    a_bounds b_bounds ?_ ?_) (bound depth depth_large)
  · exact LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) ⟨_, rfl⟩
  · exact LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) ⟨_, rfl⟩

end LambdaCantor.Classical
