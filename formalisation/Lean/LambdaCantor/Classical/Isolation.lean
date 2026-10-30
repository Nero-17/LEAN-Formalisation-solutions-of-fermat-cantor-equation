import LambdaCantor.Classical.LocalUniqueness

noncomputable section
namespace LambdaCantor.Classical

def tailAddress (digits : ℕ → Bool) (depth : ℕ) : ℝ :=
  address (1 / 3) (fun j => digits (j + depth))

theorem tailAddress_bounds (digits : ℕ → Bool) (depth : ℕ) :
    tailAddress digits depth ∈ Set.Icc (0 : ℝ) 1 :=
  LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) ⟨_, rfl⟩

theorem tailAddress_step (digits : ℕ → Bool) (depth : ℕ) :
    tailAddress digits depth = ternaryChild (digits depth) (tailAddress digits (depth + 1)) := by
  unfold tailAddress
  rw [address_first_digit (by norm_num) (by norm_num)]
  have shift : (fun j => digits (j + 1 + depth)) = (fun j => digits (j + (depth + 1))) := by
    funext j
    congr 1
    omega
  rw [shift]
  simp only [Nat.zero_add, ternaryChild]
  cases digit : digits depth <;> simp [digit] <;> ring

def curvatureError (depth : ℕ) : ℝ := (5 / 10188 : ℝ) * (1 / 3 : ℝ) ^ depth

theorem curvatureError_nonnegative (depth : ℕ) : 0 ≤ curvatureError depth := by
  unfold curvatureError
  positivity

theorem curvatureError_tendsto : Filter.Tendsto curvatureError Filter.atTop (nhds 0) := by
  have geometric : Filter.Tendsto (fun depth : ℕ => (1 / 3 : ℝ) ^ depth)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  have constant : Filter.Tendsto (fun _ : ℕ => (5 / 10188 : ℝ))
      Filter.atTop (nhds (5 / 10188)) := tendsto_const_nhds
  change Filter.Tendsto (fun depth : ℕ => (5 / 10188 : ℝ) * (1 / 3 : ℝ) ^ depth)
    Filter.atTop (nhds 0)
  simpa only [mul_zero] using constant.mul geometric

theorem curvatureError_vanishes :
    ∀ error > 0, ∃ start, ∀ depth ≥ start, curvatureError depth < error := by
  intro error positive
  exact Filter.eventually_atTop.mp ((tendsto_order.mp curvatureError_tendsto).2 error positive)

/-- Isolation of a true source-level point forces asymptotic exclusive-domain bounds. -/
theorem isolated_level_eventually_exclusive (first second : ℕ → Bool)
    (level : cylinderPolynomial (address (1 / 3) first) (address (1 / 3) second) = 3 ^ 16)
    (radius : ℝ) (radius_positive : 0 < radius)
    (isolated : ∀ point ∈ sourceLevel,
      dist point (address (1 / 3) first, address (1 / 3) second) < radius →
        point = (address (1 / 3) first, address (1 / 3) second)) :
    ∃ start, ∀ depth ≥ start,
      exclusiveLower ((6336 + address (1 / 3) first) / (9 * (566 + address (1 / 3) second)))
          (first depth) (second depth) - curvatureError depth ≤
        (((6336 + address (1 / 3) first) / (9 * (566 + address (1 / 3) second))) *
          tailAddress first depth + tailAddress second depth) / 2 ∧
      (((6336 + address (1 / 3) first) / (9 * (566 + address (1 / 3) second))) *
          tailAddress first depth + tailAddress second depth) / 2 ≤
        exclusiveUpper ((6336 + address (1 / 3) first) / (9 * (566 + address (1 / 3) second)))
          (first depth) (second depth) + curvatureError depth := by
  have first_bounds : address (1 / 3) first ∈ Set.Icc (0 : ℝ) 1 :=
    LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) ⟨_, rfl⟩
  have second_bounds : address (1 / 3) second ∈ Set.Icc (0 : ℝ) 1 :=
    LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) ⟨_, rfl⟩
  have slope_bounds := cylinder_ratio_bounds _ _ first_bounds second_bounds
  obtain ⟨ballStart, ball_bound⟩ := cylinder_eventually_in_ball first second radius radius_positive
  obtain ⟨errorStart, error_bound⟩ := curvatureError_vanishes
    (min (1 / 3) ((((6336 + address (1 / 3) first) /
      (9 * (566 + address (1 / 3) second))) - 1) / 3))
    (lt_min (by norm_num) (by linarith [slope_bounds.1]))
  refine ⟨max ballStart errorStart, ?_⟩
  intro depth depth_large
  have first_prefix_bounds := prefix_square_bounds first depth
  have second_prefix_bounds := prefix_square_bounds second depth
  have unique : ∀ x y : ℝ, x ∈ cantorSet (1 / 3) → y ∈ cantorSet (1 / 3) →
      cylinderPolynomial (prefixValue (1 / 3) first depth + (1 / 3 : ℝ) ^ depth * x)
          (prefixValue (1 / 3) second depth + (1 / 3 : ℝ) ^ depth * y) =
        cylinderPolynomial (address (1 / 3) first) (address (1 / 3) second) →
      prefixValue (1 / 3) first depth + (1 / 3 : ℝ) ^ depth * x = address (1 / 3) first ∧
      prefixValue (1 / 3) second depth + (1 / 3 : ℝ) ^ depth * y = address (1 / 3) second := by
    intro x y x_member y_member value
    have same := isolated
      (prefixValue (1 / 3) first depth + (1 / 3 : ℝ) ^ depth * x,
        prefixValue (1 / 3) second depth + (1 / 3 : ℝ) ^ depth * y)
      ⟨⟨prefix_cantor_embedding first depth x_member,
        prefix_cantor_embedding second depth y_member⟩, value.trans level⟩
      (ball_bound depth (by omega) x y
        (LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) x_member)
        (LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) y_member))
    exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩
  apply unique_square_exclusive
    (prefixValue (1 / 3) first depth) (prefixValue (1 / 3) second depth)
    (address (1 / 3) first) (address (1 / 3) second)
    (tailAddress first depth) (tailAddress second depth) ((1 / 3 : ℝ) ^ depth)
    (first depth) (second depth) (tailAddress first (depth + 1)) (tailAddress second (depth + 1))
    first_prefix_bounds.1 second_prefix_bounds.1 (by positivity)
    first_prefix_bounds.2 second_prefix_bounds.2
    (tailAddress_bounds first depth) (tailAddress_bounds second depth)
    (tailAddress_bounds first (depth + 1)) (tailAddress_bounds second (depth + 1))
    (tailAddress_step first depth) (tailAddress_step second depth)
    (address_prefix_tail (by norm_num) (by norm_num) first depth)
    (address_prefix_tail (by norm_num) (by norm_num) second depth) unique
    (by linarith [slope_bounds.1])
  · exact lt_of_lt_of_le (error_bound depth (by omega)) (min_le_left _ _)
  · exact lt_of_lt_of_le (error_bound depth (by omega)) (min_le_right _ _)

end LambdaCantor.Classical
