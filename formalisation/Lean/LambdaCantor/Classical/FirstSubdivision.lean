import LambdaCantor.Classical.Source
import LambdaCantor.Addresses

noncomputable section
namespace LambdaCantor.Classical

theorem source_level_coordinate_lower (a b : ℝ)
    (first_bounds : a ∈ Set.Icc (0 : ℝ) 1) (second_bounds : b ∈ Set.Icc (0 : ℝ) 1)
    (level : cylinderPolynomial a b = 3 ^ 16) : 1 / 3 < a ∧ 1 / 3 < b := by
  constructor
  · by_contra not_greater
    have first_upper : a ≤ 1 / 3 := le_of_not_gt not_greater
    have first_square : a ^ 2 ≤ 1 / 9 := by
      nlinarith [mul_nonneg first_bounds.1 (by linarith : 0 ≤ 1 / 3 - a)]
    have second_square : b ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg second_bounds.1 (by linarith [second_bounds.2] : 0 ≤ 1 - b)]
    unfold cylinderPolynomial at level
    nlinarith [second_bounds.2]
  · by_contra not_greater
    have second_upper : b ≤ 1 / 3 := le_of_not_gt not_greater
    have second_square : b ^ 2 ≤ 1 / 9 := by
      nlinarith [mul_nonneg second_bounds.1 (by linarith : 0 ≤ 1 / 3 - b)]
    have first_square : a ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg first_bounds.1 (by linarith [first_bounds.2] : 0 ≤ 1 - a)]
    unfold cylinderPolynomial at level
    nlinarith [first_bounds.2]

/-- Only the first child with both ternary digits two can survive. -/
theorem source_first_digits_true (first second : ℕ → Bool)
    (level : cylinderPolynomial (address (1 / 3) first) (address (1 / 3) second) = 3 ^ 16) :
    first 0 = true ∧ second 0 = true := by
  have first_bounds : address (1 / 3) first ∈ Set.Icc (0 : ℝ) 1 :=
    LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) ⟨_, rfl⟩
  have second_bounds : address (1 / 3) second ∈ Set.Icc (0 : ℝ) 1 :=
    LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) ⟨_, rfl⟩
  have lower := source_level_coordinate_lower _ _ first_bounds second_bounds level
  have force (digits : ℕ → Bool) (value_lower : 1 / 3 < address (1 / 3) digits) :
      digits 0 = true := by
    have step := address_first_digit (ratio := (1 / 3 : ℝ)) (by norm_num) (by norm_num) digits
    have tail_bounds : address (1 / 3) (fun j => digits (j + 1)) ∈ Set.Icc (0 : ℝ) 1 :=
      LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) ⟨_, rfl⟩
    cases digit : digits 0
    · simp only [digit, Bool.false_eq_true, if_false, mul_zero, zero_add] at step
      linarith [tail_bounds.2]
    · rfl
  exact ⟨force first lower.1, force second lower.2⟩

theorem cylinder_ratio_enclosure (a b : ℝ)
    (first_bounds : a ∈ Set.Icc (0 : ℝ) 1) (second_bounds : b ∈ Set.Icc (0 : ℝ) 1) :
    704 / 567 ≤ (6336 + a) / (9 * (566 + b)) ∧
      (6336 + a) / (9 * (566 + b)) ≤ 6337 / 5094 := by
  have positive : 0 < 9 * (566 + b) := by linarith [second_bounds.1]
  constructor
  · apply (le_div_iff₀ positive).mpr
    nlinarith [first_bounds.1, second_bounds.2]
  · apply (div_le_iff₀ positive).mpr
    nlinarith [first_bounds.2, second_bounds.1]

theorem normal_band_exact_margins :
    (704 / 567 : ℝ) - 11 / 9 = 11 / 567 ∧
      (2027 / 1624 : ℝ) - 6337 / 5094 = 17125 / 4136328 := by
  norm_num

theorem cylinder_normal_identity (a b : ℝ) (denominator_nonzero : 566 + b ≠ 0) :
    (6336 + a) / (9 * (566 + b)) =
      ((6336 + a) / 3 ^ 8) / (3 * ((566 + b) / 3 ^ 7)) := by
  field_simp
  ring

end LambdaCantor.Classical
