import LambdaCantor.Circle.RootExistence
import LambdaCantor.Circle.Cylinders
import LambdaCantor.First.AddressParameter

noncomputable section
namespace LambdaCantor.Circle

/-- The two root-construction coordinates are genuine Cantor points. -/
theorem root_coordinates_mem {ratio firstTail secondTail : ℝ} (depth : ℕ)
    (positive : 0 < ratio) (less_one : ratio < 1)
    (first_mem : firstTail ∈ cantorSet ratio) (second_mem : secondTail ∈ cantorSet ratio) :
    ((1 - ratio) * ratio ^ depth + ratio * (ratio ^ depth) ^ 3 * firstTail) ∈ cantorSet ratio ∧
    (1 - ratio * (ratio ^ depth) ^ 2 + ratio * (ratio ^ depth) ^ 4 * secondTail) ∈ cantorSet ratio := by
  have power_two : ratio ^ (2 * depth) = (ratio ^ depth) ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
  have first_scaled := scaled_mem_cantorSet positive.le less_one first_mem (2 * depth)
  have first_outer : 1 - ratio + ratio * (ratio ^ (2 * depth) * firstTail) ∈ cantorSet ratio := by
    rw [cantorSet_selfsimilar positive.le less_one]
    exact Or.inr ⟨ratio ^ (2 * depth) * firstTail, first_scaled, rfl⟩
  have first_coordinate := scaled_mem_cantorSet positive.le less_one first_outer depth
  have second_scaled := scaled_mem_cantorSet positive.le less_one second_mem (2 * depth)
  have second_complement := one_sub_mem_cantorSet positive.le less_one second_scaled
  have second_outer := scaled_mem_cantorSet positive.le less_one second_complement (2 * depth + 1)
  have second_coordinate := one_sub_mem_cantorSet positive.le less_one second_outer
  constructor
  · convert first_coordinate using 1 <;> rw [power_two] <;> ring
  · convert second_coordinate using 1 <;> rw [pow_succ, power_two] <;> ring

/-- Each fixed address pair has a circle root in the asserted parameter range.
This statement includes exact Cantor membership, but claims no transversality. -/
theorem circle_root_exists_for_addresses (depth : ℕ) (depth_large : 2 ≤ depth)
    (firstDigits secondDigits : ℕ → Bool) :
    ∃ ratio ∈ Set.Ioo onset (7 / 25 : ℝ),
      ∃ x ∈ cantorSet ratio, ∃ y ∈ cantorSet ratio,
      x = (1 - ratio) * ratio ^ depth + ratio * (ratio ^ depth) ^ 3 * address ratio firstDigits ∧
      y = 1 - ratio * (ratio ^ depth) ^ 2 + ratio * (ratio ^ depth) ^ 4 * address ratio secondDigits ∧
      x ^ 2 + y ^ 2 = 1 := by
  have continuity (digits : ℕ → Bool) : ContinuousOn (fun ratio => address ratio digits)
      (Set.Icc onset (7 / 25 : ℝ)) := by
    intro ratio member
    exact (hasDerivAt_address_parameter (lt_of_lt_of_le onset_pos member.1)
      (lt_of_le_of_lt member.2 (by norm_num)) digits).continuousAt.continuousWithinAt
  have bounds (digits : ℕ → Bool) : ∀ ratio ∈ Set.Icc onset (7 / 25 : ℝ),
      0 ≤ address ratio digits ∧ address ratio digits ≤ 1 := by
    intro ratio member
    exact cantorSet_subset_unitInterval (le_trans onset_pos.le member.1)
      (lt_of_le_of_lt member.2 (by norm_num)) (Set.mem_range_self digits)
  obtain ⟨ratio, member, equation⟩ := circle_root_exists_of_continuous_tails depth depth_large
    (fun ratio => address ratio firstDigits) (fun ratio => address ratio secondDigits)
    (continuity firstDigits) (continuity secondDigits) (bounds firstDigits) (bounds secondDigits)
  have memberships := root_coordinates_mem depth (lt_trans onset_pos member.1)
    (lt_trans member.2 (by norm_num)) (Set.mem_range_self firstDigits) (Set.mem_range_self secondDigits)
  exact ⟨ratio, member, _, memberships.1, _, memberships.2, rfl, rfl, equation⟩

end LambdaCantor.Circle

