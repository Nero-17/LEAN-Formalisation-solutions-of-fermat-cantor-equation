import LambdaCantor.Basic
import LambdaCantor.SelfSimilarity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor.First.LinearRegularity

/-- Digits retained at positions divisible by the block length. -/
def sparseDigits (blockLength : ℕ) (digits : ℕ → Bool) (index : ℕ) : Bool :=
  if index % blockLength = 0 then digits index else false

/-- The complementary digits; the sparse positions are replaced by zero. -/
def denseDigits (blockLength : ℕ) (digits : ℕ → Bool) (index : ℕ) : Bool :=
  if index % blockLength = 0 then false else digits index

/-- Exact splitting of each actual Cantor address into sparse and dense
positions. No probabilistic independence is assumed or claimed here. -/
theorem address_digit_split {ratio : ℝ} (hpos : 0 ≤ ratio) (hlt : ratio < 1)
    (blockLength : ℕ) (digits : ℕ → Bool) :
    address ratio digits = address ratio (sparseDigits blockLength digits) +
      address ratio (denseDigits blockLength digits) := by
  have hterm (index : ℕ) :
      (if digits index then (1 : ℝ) else 0) * ratio ^ index =
        (if sparseDigits blockLength digits index then (1 : ℝ) else 0) * ratio ^ index +
        (if denseDigits blockLength digits index then (1 : ℝ) else 0) * ratio ^ index := by
    unfold sparseDigits denseDigits
    split_ifs <;> simp_all
  unfold address
  rw [← mul_add, ← Summable.tsum_add
    (address_summable hpos hlt (sparseDigits blockLength digits))
    (address_summable hpos hlt (denseDigits blockLength digits))]
  congr 1
  exact tsum_congr hterm

/-- The paired linear projection splits into the actual two digit factors. -/
theorem paired_projection_digit_split {ratio : ℝ} (hpos : 0 ≤ ratio) (hlt : ratio < 1)
    (slope : ℝ) (blockLength : ℕ) (leftDigits rightDigits : ℕ → Bool) :
    slope * address ratio leftDigits + address ratio rightDigits =
      (slope * address ratio (sparseDigits blockLength leftDigits) +
        address ratio (sparseDigits blockLength rightDigits)) +
      (slope * address ratio (denseDigits blockLength leftDigits) +
        address ratio (denseDigits blockLength rightDigits)) := by
  rw [address_digit_split hpos hlt blockLength leftDigits,
    address_digit_split hpos hlt blockLength rightDigits]
  ring

/-- A block length exists with strict L2 similarity surplus whenever the
parameter interval lies strictly above one quarter. -/
theorem exists_supercritical_block_length {lower : ℝ} (hlower : (1 / 4 : ℝ) < lower) :
    ∃ blockLength : ℕ, 1 ≤ blockLength ∧
      1 < (4 : ℝ) ^ (blockLength - 1) * lower ^ blockLength := by
  have hpower := tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 4 * lower by linarith)
  obtain ⟨blockLength, hlength, hlarge⟩ :=
    ((Filter.eventually_ge_atTop (1 : ℕ)).and
      (hpower.eventually (Filter.eventually_gt_atTop (4 : ℝ)))).exists
  refine ⟨blockLength, hlength, ?_⟩
  have hfour : (4 : ℝ) ^ blockLength = (4 : ℝ) ^ (blockLength - 1) * 4 := by
    rw [← pow_succ, Nat.sub_add_cancel hlength]
  rw [mul_pow, hfour] at hlarge
  nlinarith

/-- The actual equal-weight atomic mass inequality required by the external
L2 theorem follows from the block surplus, uniformly above the lower endpoint. -/
theorem supercritical_block_mass {lower ratio : ℝ} (hlower : 0 ≤ lower) (hratio : lower ≤ ratio)
    (blockLength : ℕ) (hsurplus : 1 < (4 : ℝ) ^ (blockLength - 1) * lower ^ blockLength) :
    ((4 ^ (blockLength - 1) : ℕ) : ℝ)⁻¹ < ratio ^ blockLength := by
  have hcard : 0 < ((4 ^ (blockLength - 1) : ℕ) : ℝ) := by positivity
  have hpower := pow_le_pow_left₀ hlower hratio blockLength
  have hproduct := mul_le_mul_of_nonneg_left hpower hcard.le
  rw [← one_div]
  apply (div_lt_iff₀ hcard).mpr
  push_cast at *
  nlinarith

/-- Strong separation makes distinct paired infinite addresses nondegenerate
under variation of the slope, even with the contraction held fixed. -/
theorem paired_address_projection_nondegenerate {ratio lowerSlope upperSlope : ℝ}
    (hratio : 0 < ratio) (hhalf : ratio < 1 / 2) (hslopes : lowerSlope < upperSlope)
    (left right : (ℕ → Bool) × (ℕ → Bool)) (hne : left ≠ right) :
    ∃ slope ∈ Set.Ioo lowerSlope upperSlope,
      slope * address ratio left.1 + address ratio left.2 ≠
        slope * address ratio right.1 + address ratio right.2 := by
  by_contra hnone
  push_neg at hnone
  have hfirst := hnone ((2 * lowerSlope + upperSlope) / 3) (by constructor <;> linarith)
  have hsecond := hnone ((lowerSlope + 2 * upperSlope) / 3) (by constructor <;> linarith)
  have hproduct : (upperSlope - lowerSlope) * (address ratio left.1 - address ratio right.1) = 0 := by
    nlinarith
  have hleft : address ratio left.1 = address ratio right.1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_left (ne_of_gt (sub_pos.mpr hslopes)))
  have hright : address ratio left.2 = address ratio right.2 := by
    rw [hleft] at hfirst
    linarith
  apply hne
  exact Prod.ext (address_injective hratio hhalf hleft) (address_injective hratio hhalf hright)

end LambdaCantor.First.LinearRegularity

