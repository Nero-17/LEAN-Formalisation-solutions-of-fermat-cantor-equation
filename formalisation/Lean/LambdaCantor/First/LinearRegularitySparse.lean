import LambdaCantor.First.LinearRegularityDigits
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace LambdaCantor.First.LinearRegularity

/-- Reindexing the sparse digit positions identifies their actual address
with an affine rescaling of the Bernoulli address at contraction lambda^M. -/
theorem sparse_address_rescaling {ratio : ℝ} (hpos : 0 ≤ ratio) (hlt : ratio < 1)
    (blockLength : ℕ) (hblockLength : 0 < blockLength) (digits : ℕ → Bool) :
    address ratio (sparseDigits blockLength digits) =
      ((1 - ratio) / (1 - ratio ^ blockLength)) *
        address (ratio ^ blockLength) (fun index => digits (blockLength * index)) := by
  have hinjective : Function.Injective (fun index : ℕ => blockLength * index) := by
    intro left right hequal
    exact mul_left_cancel₀ (Nat.ne_of_gt hblockLength) hequal
  have hsupport : Function.support
      (fun index : ℕ => (if sparseDigits blockLength digits index then (1 : ℝ) else 0) * ratio ^ index) ⊆
      Set.range (fun index : ℕ => blockLength * index) := by
    intro index hindex
    have hmod : index % blockLength = 0 := by
      by_contra hmod
      exact hindex (by simp [sparseDigits, hmod])
    obtain ⟨quotient, hequal⟩ := Nat.dvd_of_mod_eq_zero hmod
    exact ⟨quotient, hequal.symm⟩
  have hsum := hinjective.tsum_eq hsupport
  have hreindex :
      (∑' index : ℕ, (if sparseDigits blockLength digits index then (1 : ℝ) else 0) * ratio ^ index) =
      ∑' index : ℕ, (if digits (blockLength * index) then (1 : ℝ) else 0) *
        (ratio ^ blockLength) ^ index := by
    simpa [sparseDigits, Nat.mul_mod, pow_mul] using hsum.symm
  have hnonzero : 1 - ratio ^ blockLength ≠ 0 := by
    have hpower := pow_lt_one₀ hpos hlt (Nat.ne_of_gt hblockLength)
    linarith
  unfold address
  rw [hreindex]
  field_simp [hnonzero]

end LambdaCantor.First.LinearRegularity
