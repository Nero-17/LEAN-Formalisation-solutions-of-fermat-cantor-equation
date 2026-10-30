import LambdaCantor.Addresses
import Mathlib.Algebra.Ring.GeomSum

noncomputable section

namespace LambdaCantor.AE

def zeroPrefixDigits (depth : ℕ) (digits : ℕ → Bool) (index : ℕ) : Bool :=
  if index < depth then digits index else false

def pairedZeroPrefixDigits (depth : ℕ) (digits : ℕ → Bool × Bool) (index : ℕ) : Bool × Bool :=
  (zeroPrefixDigits depth (fun position => (digits position).1) index,
    zeroPrefixDigits depth (fun position => (digits position).2) index)

theorem pairedZeroPrefixDigits_agrees (depth : ℕ) (digits : ℕ → Bool × Bool) :
    ∀ index < depth, digits index = pairedZeroPrefixDigits depth digits index := by
  intro index before
  simp [pairedZeroPrefixDigits, zeroPrefixDigits, before]

theorem prefixValue_bounds {ratio : ℝ} (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (digits : ℕ → Bool) (depth : ℕ) :
    0 ≤ prefixValue ratio digits depth ∧ prefixValue ratio digits depth+ratio^depth ≤ 1 := by
  have gap_nonnegative : 0 ≤ 1-ratio := by linarith
  have summands_nonnegative : ∀ index ∈ Finset.range depth,
      0 ≤ (if digits index then (1 : ℝ) else 0)*ratio^index := by
    intro index _
    split_ifs <;> positivity
  have sum_bound : (∑ index ∈ Finset.range depth,
      (if digits index then (1 : ℝ) else 0)*ratio^index) ≤ ∑ index ∈ Finset.range depth, ratio^index := by
    apply Finset.sum_le_sum
    intro index _
    split_ifs <;> simp [pow_nonneg nonnegative]
  have prefix_bound : prefixValue ratio digits depth ≤ 1-ratio^depth := by
    unfold prefixValue
    apply (mul_le_mul_of_nonneg_left sum_bound gap_nonnegative).trans_eq
    rw [mul_comm]
    exact geom_sum_mul_neg ratio depth
  exact ⟨mul_nonneg gap_nonnegative (Finset.sum_nonneg summands_nonnegative), by linarith⟩

theorem prefixValue_zeroPrefixDigits (ratio : ℝ) (digits : ℕ → Bool) (depth : ℕ) :
    prefixValue ratio (zeroPrefixDigits depth digits) depth = prefixValue ratio digits depth := by
  unfold prefixValue
  congr 1
  apply Finset.sum_congr rfl
  intro index membership
  simp only [zeroPrefixDigits, if_pos (Finset.mem_range.mp membership)]

theorem address_zeroPrefixDigits {ratio : ℝ} (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (digits : ℕ → Bool) (depth : ℕ) :
    address ratio (zeroPrefixDigits depth digits) = prefixValue ratio digits depth := by
  rw [address_prefix_tail nonnegative less_one _ depth, prefixValue_zeroPrefixDigits]
  have tail_zero : (fun index => zeroPrefixDigits depth digits (index+depth)) = fun _ => false := by
    funext index
    simp [zeroPrefixDigits, show ¬index+depth < depth by omega]
  rw [tail_zero]
  simp [address]

theorem address_prefix_zero_tail {ratio : ℝ} (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (digits : ℕ → Bool) (depth : ℕ) :
    address ratio digits = address ratio (zeroPrefixDigits depth digits) +
      ratio^depth*address ratio (fun index => digits (index+depth)) := by
  rw [address_zeroPrefixDigits nonnegative less_one, address_prefix_tail nonnegative less_one digits depth]

theorem address_zeroPrefixDigits_bounds {ratio : ℝ} (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (digits : ℕ → Bool) (depth : ℕ) :
    0 ≤ address ratio (zeroPrefixDigits depth digits) ∧
      address ratio (zeroPrefixDigits depth digits)+ratio^depth ≤ 1 := by
  rw [address_zeroPrefixDigits nonnegative less_one]
  exact prefixValue_bounds nonnegative less_one digits depth

end LambdaCantor.AE
