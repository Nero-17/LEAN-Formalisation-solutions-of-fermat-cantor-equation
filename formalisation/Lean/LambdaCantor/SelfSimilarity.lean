import LambdaCantor.Addresses
import Mathlib.Tactic.SplitIfs

noncomputable section
namespace LambdaCantor

def prependDigit (digit : Bool) (digits : ℕ → Bool) : ℕ → Bool
  | 0 => digit
  | j + 1 => digits j

theorem address_prepend {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (digit : Bool) (digits : ℕ → Bool) :
    address ratio (prependDigit digit digits) =
      (1 - ratio) * (if digit then (1 : ℝ) else 0) + ratio * address ratio digits := by
  rw [address_first_digit nonnegative less_one]
  rfl

theorem cantorSet_selfsimilar {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) :
    cantorSet ratio = (fun x => ratio * x) '' cantorSet ratio ∪
      (fun x => 1 - ratio + ratio * x) '' cantorSet ratio := by
  ext x
  constructor
  · rintro ⟨digits, rfl⟩
    have decomposition := address_first_digit nonnegative less_one digits
    cases digit_value : digits 0
    · left
      exact ⟨address ratio (fun j => digits (j + 1)), ⟨_, rfl⟩,
        by simpa [digit_value] using decomposition.symm⟩
    · right
      exact ⟨address ratio (fun j => digits (j + 1)), ⟨_, rfl⟩,
        by simpa [digit_value] using decomposition.symm⟩
  · rintro (⟨y, ⟨digits, rfl⟩, rfl⟩ | ⟨y, ⟨digits, rfl⟩, rfl⟩)
    · exact ⟨prependDigit false digits, by simp [address_prepend nonnegative less_one]⟩
    · exact ⟨prependDigit true digits, by simp [address_prepend nonnegative less_one]⟩

theorem first_digit_gap {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_half : ratio < 1 / 2) (left right : ℕ → Bool)
    (different : left 0 ≠ right 0) :
    1 - 2 * ratio ≤ |address ratio left - address ratio right| := by
  have less_one : ratio < 1 := by linarith
  have left_bounds := cantorSet_subset_unitInterval nonnegative less_one
    (show address ratio (fun j => left (j + 1)) ∈ cantorSet ratio from ⟨_, rfl⟩)
  have right_bounds := cantorSet_subset_unitInterval nonnegative less_one
    (show address ratio (fun j => right (j + 1)) ∈ cantorSet ratio from ⟨_, rfl⟩)
  rcases left_bounds with ⟨left_nonnegative, left_le_one⟩
  rcases right_bounds with ⟨right_nonnegative, right_le_one⟩
  rw [address_first_digit nonnegative less_one left,
    address_first_digit nonnegative less_one right]
  cases left_digit : left 0 <;> cases right_digit : right 0 <;>
    simp only [left_digit, right_digit, if_true, Bool.false_eq_true, if_false,
      mul_one, mul_zero, zero_add] at different ⊢
  · exact False.elim (different rfl)
  · apply le_trans _ (neg_le_abs _)
    nlinarith
  · apply le_trans _ (le_abs_self _)
    nlinarith
  · exact False.elim (different rfl)

theorem prefix_separation {ratio : ℝ} (positive : 0 < ratio)
    (less_half : ratio < 1 / 2) (left right : ℕ → Bool) (depth : ℕ)
    (agreement : ∀ j < depth, left j = right j) (different : left depth ≠ right depth) :
    (1 - 2 * ratio) * ratio ^ depth ≤ |address ratio left - address ratio right| := by
  have less_one : ratio < 1 := by linarith
  have equal_prefix : prefixValue ratio left depth = prefixValue ratio right depth := by
    unfold prefixValue
    congr 1
    apply Finset.sum_congr rfl
    intro j membership
    rw [agreement j (Finset.mem_range.mp membership)]
  rw [address_prefix_tail positive.le less_one left depth,
    address_prefix_tail positive.le less_one right depth, equal_prefix,
    add_sub_add_left_eq_sub, ← mul_sub, abs_mul,
    abs_of_nonneg (pow_nonneg positive.le depth)]
  rw [mul_comm (1 - 2 * ratio)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg positive.le depth)
  exact first_digit_gap positive.le less_half (fun j => left (j + depth))
    (fun j => right (j + depth)) (by simpa using different)

theorem address_injective {ratio : ℝ} (positive : 0 < ratio)
    (less_half : ratio < 1 / 2) : Function.Injective (address ratio) := by
  intro left right equal_values
  by_contra different_sequences
  have exists_difference : ∃ depth, left depth ≠ right depth := by
    by_contra no_difference
    apply different_sequences
    funext depth
    by_contra different
    exact no_difference ⟨depth, different⟩
  have separation := prefix_separation positive less_half left right
    (Nat.find exists_difference)
    (fun j before => not_ne_iff.mp (Nat.find_min exists_difference before))
    (Nat.find_spec exists_difference)
  rw [equal_values, sub_self, abs_zero] at separation
  have strictly_positive : 0 < (1 - 2 * ratio) * ratio ^ Nat.find exists_difference :=
    mul_pos (by linarith) (pow_pos positive _)
  linarith

end LambdaCantor
