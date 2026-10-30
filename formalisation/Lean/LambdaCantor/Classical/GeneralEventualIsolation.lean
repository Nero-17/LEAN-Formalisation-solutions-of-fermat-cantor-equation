import LambdaCantor.Classical.Isolation
import LambdaCantor.Classical.GeneralIsolation

noncomputable section
namespace LambdaCantor.Classical

def cantorLevel (function : ℝ → ℝ → ℝ) (target : ℝ) : Set (ℝ × ℝ) :=
  (cantorSet (1 / 3) ×ˢ cantorSet (1 / 3)) ∩
    {point | function point.1 point.2 = target}

/-- The geometric isolation argument, independent of the particular defining function.
The remaining analytic input is a normalized first-order error tending to zero. -/
theorem general_isolated_level_eventually_exclusive (function : ℝ → ℝ → ℝ)
    (first second : ℕ → Bool) (slope : ℝ) (slope_greater : 1 < slope)
    (errors : ℕ → ℝ)
    (vanishing : ∀ error > 0, ∃ start, ∀ depth ≥ start, errors depth < error)
    (approximationStart : ℕ)
    (approximation : ∀ depth ≥ approximationStart,
      SquareApproximation function (prefixValue (1 / 3) first depth)
        (prefixValue (1 / 3) second depth)
        (address (1 / 3) first) (address (1 / 3) second)
        (tailAddress first depth) (tailAddress second depth) ((1 / 3 : ℝ)^depth)
        slope (errors depth))
    (radius : ℝ) (radius_positive : 0 < radius)
    (isolated : ∀ point ∈ cantorLevel function
      (function (address (1 / 3) first) (address (1 / 3) second)),
      dist point (address (1 / 3) first, address (1 / 3) second) < radius →
        point = (address (1 / 3) first, address (1 / 3) second)) :
    ∃ start, ∀ depth ≥ start,
      exclusiveLower slope (first depth) (second depth) - errors depth ≤
        (slope * tailAddress first depth + tailAddress second depth) / 2 ∧
      (slope * tailAddress first depth + tailAddress second depth) / 2 ≤
        exclusiveUpper slope (first depth) (second depth) + errors depth := by
  have first_bounds : address (1 / 3) first ∈ Set.Icc (0 : ℝ) 1 :=
    LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) ⟨_, rfl⟩
  have second_bounds : address (1 / 3) second ∈ Set.Icc (0 : ℝ) 1 :=
    LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) ⟨_, rfl⟩
  obtain ⟨ballStart, ball_bound⟩ := cylinder_eventually_in_ball first second radius radius_positive
  obtain ⟨errorStart, error_bound⟩ := vanishing
    (min (1 / 3) ((slope - 1) / 3))
    (lt_min (by norm_num) (by linarith))
  refine ⟨max (max ballStart errorStart) approximationStart, ?_⟩
  intro depth depth_large
  have first_prefix_bounds := prefix_square_bounds first depth
  have second_prefix_bounds := prefix_square_bounds second depth
  have unique : ∀ x y : ℝ, x ∈ cantorSet (1 / 3) → y ∈ cantorSet (1 / 3) →
      function (prefixValue (1 / 3) first depth + (1 / 3 : ℝ) ^ depth * x)
          (prefixValue (1 / 3) second depth + (1 / 3 : ℝ) ^ depth * y) =
        function (address (1 / 3) first) (address (1 / 3) second) →
      prefixValue (1 / 3) first depth + (1 / 3 : ℝ) ^ depth * x = address (1 / 3) first ∧
      prefixValue (1 / 3) second depth + (1 / 3 : ℝ) ^ depth * y = address (1 / 3) second := by
    intro x y x_member y_member value
    have same := isolated
      (prefixValue (1 / 3) first depth + (1 / 3 : ℝ) ^ depth * x,
        prefixValue (1 / 3) second depth + (1 / 3 : ℝ) ^ depth * y)
      ⟨⟨prefix_cantor_embedding first depth x_member,
        prefix_cantor_embedding second depth y_member⟩, value⟩
      (ball_bound depth (by omega) x y
        (LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) x_member)
        (LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) y_member))
    exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩
  apply general_unique_square_exclusive function slope (errors depth)
    (prefixValue (1 / 3) first depth) (prefixValue (1 / 3) second depth)
    (address (1 / 3) first) (address (1 / 3) second)
    (tailAddress first depth) (tailAddress second depth) ((1 / 3 : ℝ) ^ depth)
    (approximation depth (by omega))
    (first depth) (second depth) (tailAddress first (depth + 1)) (tailAddress second (depth + 1))
    first_prefix_bounds.1 second_prefix_bounds.1 (by positivity)
    first_prefix_bounds.2 second_prefix_bounds.2
    (tailAddress_bounds first depth) (tailAddress_bounds second depth)
    (tailAddress_bounds first (depth + 1)) (tailAddress_bounds second (depth + 1))
    (tailAddress_step first depth) (tailAddress_step second depth)
    (address_prefix_tail (by norm_num) (by norm_num) first depth)
    (address_prefix_tail (by norm_num) (by norm_num) second depth) unique
    (by linarith)
  · exact lt_of_lt_of_le (error_bound depth (by omega)) (min_le_left _ _)
  · exact lt_of_lt_of_le (error_bound depth (by omega)) (min_le_right _ _)

end LambdaCantor.Classical
