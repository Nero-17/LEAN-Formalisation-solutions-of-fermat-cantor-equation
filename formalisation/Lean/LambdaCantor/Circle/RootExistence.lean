import LambdaCantor.Circle.RootEndpoint

noncomputable section
namespace LambdaCantor.Circle

def circleRootResidual (depth : ℕ) (firstTail secondTail : ℝ → ℝ) (ratio : ℝ) : ℝ :=
  -(4 * ratio - 1 - ratio ^ 2) +
    2 * ratio * (ratio ^ depth) ^ 2 * ((1 - ratio) * firstTail ratio + secondTail ratio) +
    ratio ^ 2 * (ratio ^ depth) ^ 4 * (firstTail ratio) ^ 2 +
    ratio ^ 2 * (ratio ^ depth) ^ 2 * (1 - (ratio ^ depth) ^ 2 * secondTail ratio) ^ 2

/-- The endpoint signs produce a circle root for every pair of continuous
unit-interval tails. Uniqueness and transversality are separate statements. -/
theorem circle_root_exists_of_continuous_tails (depth : ℕ) (depth_large : 2 ≤ depth)
    (firstTail secondTail : ℝ → ℝ)
    (first_continuous : ContinuousOn firstTail (Set.Icc onset (7 / 25 : ℝ)))
    (second_continuous : ContinuousOn secondTail (Set.Icc onset (7 / 25 : ℝ)))
    (first_bounds : ∀ ratio ∈ Set.Icc onset (7 / 25 : ℝ), 0 ≤ firstTail ratio ∧ firstTail ratio ≤ 1)
    (second_bounds : ∀ ratio ∈ Set.Icc onset (7 / 25 : ℝ), 0 ≤ secondTail ratio ∧ secondTail ratio ≤ 1) :
    ∃ ratio ∈ Set.Ioo onset (7 / 25 : ℝ),
      ((1 - ratio) * ratio ^ depth + ratio * (ratio ^ depth) ^ 3 * firstTail ratio) ^ 2 +
      (1 - ratio * (ratio ^ depth) ^ 2 + ratio * (ratio ^ depth) ^ 4 * secondTail ratio) ^ 2 = 1 := by
  have onset_bound : onset < (7 / 25 : ℝ) := by
    have := onset_lt_twenty_seven_hundredths
    linarith
  have left_mem : onset ∈ Set.Icc onset (7 / 25 : ℝ) := ⟨le_rfl, onset_bound.le⟩
  have right_mem : (7 / 25 : ℝ) ∈ Set.Icc onset (7 / 25 : ℝ) := ⟨onset_bound.le, le_rfl⟩
  have onset_power_lt_one : onset ^ depth < 1 := by
    have power_bound := power_antitone onset_pos.le (le_of_lt (lt_trans onset_lt_one_third (by norm_num)))
      (show 1 ≤ depth by omega)
    simp only [pow_one] at power_bound
    linarith [onset_lt_one_third]
  have left_positive : 0 < circleRootResidual depth firstTail secondTail onset :=
    onset_residual_positive _ _ _ (pow_pos onset_pos _) onset_power_lt_one
      (first_bounds onset left_mem).1 (second_bounds onset left_mem).1 (second_bounds onset left_mem).2
  have right_negative : circleRootResidual depth firstTail secondTail (7 / 25) < 0 :=
    right_endpoint_residual_negative _ _ _ (pow_nonneg (by norm_num) _)
      (power_antitone (by norm_num) (by norm_num) depth_large)
      (first_bounds _ right_mem).1 (first_bounds _ right_mem).2
      (second_bounds _ right_mem).1 (second_bounds _ right_mem).2
  have residual_continuous : ContinuousOn (circleRootResidual depth firstTail secondTail)
      (Set.Icc onset (7 / 25 : ℝ)) := by
    unfold circleRootResidual
    fun_prop
  obtain ⟨ratio, bounds, zero⟩ := intermediate_value_Icc' onset_bound.le residual_continuous
    (show (0 : ℝ) ∈ Set.Icc (circleRootResidual depth firstTail secondTail (7 / 25))
      (circleRootResidual depth firstTail secondTail onset) from ⟨right_negative.le, left_positive.le⟩)
  refine ⟨ratio, ⟨?_, ?_⟩, ?_⟩
  · exact lt_of_le_of_ne bounds.1 (by intro equality; subst ratio; linarith)
  · exact lt_of_le_of_ne bounds.2 (by intro equality; subst ratio; linarith)
  · have identity := root_residual_identity ratio (ratio ^ depth) (firstTail ratio) (secondTail ratio)
    change circleRootResidual depth firstTail secondTail ratio = 0 at zero
    unfold circleRootResidual at zero
    rw [zero, mul_zero] at identity
    linarith

end LambdaCantor.Circle
