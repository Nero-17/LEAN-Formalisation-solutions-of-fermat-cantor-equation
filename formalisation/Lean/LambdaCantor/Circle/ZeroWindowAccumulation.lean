import LambdaCantor.Circle.ZeroWindowExistence
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace LambdaCantor.Circle

/-- A uniform distance estimate for every parameter in a polynomial window. -/
theorem zero_window_distance (depth : ℕ) {ratio : ℝ}
    (above : onset < ratio) (upper : ratio ≤ (67 / 250 : ℝ))
    (window_upper : 4 * ratio - 1 - ratio ^ 2 <
      (381 / 100 : ℝ) * ratio ^ (2 * depth + 2)) :
    ratio < onset + 2 * (67 / 250 : ℝ) ^ (2 * depth + 2) := by
  have positive : 0 < ratio := lt_trans onset_pos above
  have power_bound := pow_le_pow_left₀ positive.le upper (2 * depth + 2)
  have factor_positive : 0 < 1 - ratio - onset := by
    have := onset_in_certificate_interval.2
    linarith
  have product_positive := mul_pos (sub_pos.mpr above) factor_positive
  have onset_identity := onset_equation
  have factorization : 4 * ratio - 1 - ratio ^ 2 =
      (ratio - onset) * (4 - ratio - onset) := by nlinarith
  have endpoint_power := pow_pos (by norm_num : (0 : ℝ) < 67 / 250) (2 * depth + 2)
  nlinarith

/-- Nonempty open intervals with exactly the two axis points occur in every
right neighbourhood of the onset. No dimension or measure hypothesis is used. -/
theorem zero_intervals_arbitrarily_close (epsilon : ℝ) (epsilon_positive : 0 < epsilon) :
    ∃ left right : ℝ, left < right ∧
      Set.Ioo left right ⊆ Set.Ioo onset (onset + epsilon) ∧
      ∀ ratio ∈ Set.Ioo left right, ∀ x ∈ cantorSet ratio, ∀ y ∈ cantorSet ratio,
        x ^ 2 + y ^ 2 = 1 → (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
  obtain ⟨power, power_small⟩ : ∃ power : ℕ, (67 / 250 : ℝ) ^ power < epsilon / 2 :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  have depth_large : 3 ≤ power + 3 := by omega
  have powers_ordered : power ≤ 2 * (power + 3) + 2 := by omega
  have power_bound := power_antitone (by norm_num : (0 : ℝ) ≤ 67 / 250)
    (by norm_num : (67 / 250 : ℝ) ≤ 1) powers_ordered
  obtain ⟨centre, centre_bounds, centre_equation⟩ := zero_window_centre (power + 3) depth_large
  have centre_power := pow_pos (lt_trans onset_pos centre_bounds.1) (2 * (power + 3) + 2)
  have centre_window_upper : 4 * centre - 1 - centre ^ 2 <
      (381 / 100 : ℝ) * centre ^ (2 * (power + 3) + 2) := by
    rw [centre_equation]
    nlinarith
  have centre_distance := zero_window_distance (power + 3) centre_bounds.1
    centre_bounds.2.le centre_window_upper
  have centre_near : centre < onset + epsilon := by linarith
  have open_window : IsOpen {ratio : ℝ |
      ratio ∈ Set.Ioo onset (67 / 250 : ℝ) ∧ ratio < onset + epsilon ∧
      (379 / 100 : ℝ) * ratio ^ (2 * (power + 3) + 2) < 4 * ratio - 1 - ratio ^ 2 ∧
      4 * ratio - 1 - ratio ^ 2 < (381 / 100 : ℝ) * ratio ^ (2 * (power + 3) + 2)} := by
    exact isOpen_Ioo.inter ((isOpen_lt
      (f := fun ratio : ℝ => ratio) (g := fun _ : ℝ => onset + epsilon)
      continuous_id continuous_const).inter
      ((isOpen_lt
        (f := fun ratio : ℝ => (379 / 100 : ℝ) * ratio ^ (2 * (power + 3) + 2))
        (g := fun ratio : ℝ => 4 * ratio - 1 - ratio ^ 2)
        (by fun_prop) (by fun_prop)).inter
        (isOpen_lt
          (f := fun ratio : ℝ => 4 * ratio - 1 - ratio ^ 2)
          (g := fun ratio : ℝ => (381 / 100 : ℝ) * ratio ^ (2 * (power + 3) + 2))
          (by fun_prop) (by fun_prop))))
  obtain ⟨left, right, ordered, subset⟩ := open_window.exists_Ioo_subset
    ⟨centre, centre_bounds, centre_near, by rw [centre_equation]; nlinarith,
      centre_window_upper⟩
  refine ⟨left, right, ordered, ?_, ?_⟩
  · intro ratio member
    exact ⟨(subset member).1.1, (subset member).2.1⟩
  · intro ratio member x x_mem y y_mem equation
    have conditions := subset member
    exact circle_axis_only_in_zero_window (power + 3) depth_large
      (le_trans onset_in_certificate_interval.1.le conditions.1.1.le)
      conditions.1.2.le conditions.2.2.1 conditions.2.2.2 x_mem y_mem equation

end LambdaCantor.Circle
