import LambdaCantor.Basic
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor

def prefixValue (ratio : ℝ) (digits : ℕ → Bool) (length : ℕ) : ℝ :=
  (1 - ratio) * ∑ j ∈ Finset.range length,
    (if digits j then (1 : ℝ) else 0) * ratio ^ j

theorem address_prefix_tail {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (digits : ℕ → Bool) (length : ℕ) :
    address ratio digits = prefixValue ratio digits length +
      ratio ^ length * address ratio (fun j => digits (j + length)) := by
  unfold address prefixValue
  rw [← (address_summable nonnegative less_one digits).sum_add_tsum_nat_add length]
  simp_rw [pow_add, ← mul_assoc, tsum_mul_right]
  ring

theorem address_first_digit {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (digits : ℕ → Bool) :
    address ratio digits = (1 - ratio) * (if digits 0 then (1 : ℝ) else 0) +
      ratio * address ratio (fun j => digits (j + 1)) := by
  simpa [prefixValue] using address_prefix_tail nonnegative less_one digits 1

theorem address_complement {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (digits : ℕ → Bool) :
    address ratio (fun j => !digits j) = 1 - address ratio digits := by
  have summand_eq : (fun j : ℕ => (if !digits j then (1 : ℝ) else 0) * ratio ^ j) =
      (fun j : ℕ => ratio ^ j - (if digits j then (1 : ℝ) else 0) * ratio ^ j) := by
    funext j
    cases digits j <;> simp
  unfold address
  rw [summand_eq, (summable_geometric_of_lt_one nonnegative less_one).tsum_sub
    (address_summable nonnegative less_one digits),
    tsum_geometric_of_lt_one nonnegative less_one, mul_sub,
    mul_inv_cancel₀ (show 1 - ratio ≠ 0 by linarith)]

theorem one_sub_mem_cantorSet {ratio x : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (membership : x ∈ cantorSet ratio) :
    1 - x ∈ cantorSet ratio := by
  rcases membership with ⟨digits, rfl⟩
  exact ⟨fun j => !digits j, address_complement nonnegative less_one digits⟩

theorem address_first_true_lower {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (digits : ℕ → Bool) (first_true : digits 0 = true) :
    1 - ratio ≤ address ratio digits := by
  rw [address_first_digit nonnegative less_one digits, first_true]
  simp only [if_true, mul_one]
  exact le_add_of_nonneg_right (mul_nonneg nonnegative
    (address_nonnegative nonnegative less_one _))

theorem exists_near_axis_shell {ratio x : ℝ} (positive : 0 < ratio)
    (less_one : ratio < 1) (membership : x ∈ cantorSet ratio) (nonzero : x ≠ 0) :
    ∃ depth : ℕ, ∃ tail ∈ cantorSet ratio,
      1 - ratio ≤ tail ∧ tail ≤ 1 ∧ x = ratio ^ depth * tail := by
  classical
  rcases membership with ⟨digits, rfl⟩
  have exists_true : ∃ j, digits j = true := by
    by_contra absence
    push_neg at absence
    have all_false : ∀ j, digits j = false := by
      intro j
      cases value : digits j
      · rfl
      · exact False.elim (absence j value)
    apply nonzero
    simp [address, all_false]
  refine ⟨Nat.find exists_true, address ratio (fun j => digits (j + Nat.find exists_true)),
    ⟨fun j => digits (j + Nat.find exists_true), rfl⟩, ?_,
    address_le_one positive.le less_one _, ?_⟩
  · apply address_first_true_lower positive.le less_one
    simpa using Nat.find_spec exists_true
  · rw [address_prefix_tail positive.le less_one digits (Nat.find exists_true)]
    have prefix_zero : prefixValue ratio digits (Nat.find exists_true) = 0 := by
      unfold prefixValue
      have sum_zero : (∑ j ∈ Finset.range (Nat.find exists_true),
          (if digits j then (1 : ℝ) else 0) * ratio ^ j) = 0 := by
        apply Finset.sum_eq_zero
        intro j membership
        have before := Nat.find_min exists_true (Finset.mem_range.mp membership)
        simp [before]
      rw [sum_zero, mul_zero]
    rw [prefix_zero, zero_add]

end LambdaCantor
