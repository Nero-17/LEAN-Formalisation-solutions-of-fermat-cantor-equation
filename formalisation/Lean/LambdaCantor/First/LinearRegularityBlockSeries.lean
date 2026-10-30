import LambdaCantor.First.LinearRegularityBlockLaw
import LambdaCantor.First.LinearRegularityConvolution
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

noncomputable section
open scoped BigOperators
namespace LambdaCantor.First.LinearRegularity

/-- Every retained position is in the actual block indexing range. -/
theorem denseBlockIndex_range {blockLength index : ℕ} (hblock : 0 < blockLength)
    (hmod : index % blockLength ≠ 0) :
    index ∈ Set.range (fun position : ℕ × Fin (blockLength - 1) =>
      blockLength * position.1 + position.2.val + 1) := by
  have hlt := Nat.mod_lt index hblock
  refine ⟨(index / blockLength, ⟨index % blockLength - 1, by omega⟩), ?_⟩
  have heq := Nat.mod_add_div index blockLength
  dsimp
  omega

/-- Exact series regrouping of the dense projected address into its actual
analytic block translations, under the original address coding. -/
theorem denseProjection_block_series {ratio : ℝ} (hpositive : 0 ≤ ratio) (hlt : ratio < 1)
    (slope : ℝ) (blockLength : ℕ) (hblock : 0 < blockLength) (digits : ℕ → Bool × Bool) :
    denseProjection ratio slope blockLength digits =
      ∑' block : ℕ, (ratio ^ blockLength) ^ block *
        denseBlockTranslation blockLength (ratio, slope) (denseBlockCoding blockLength digits block) := by
  let term : ℕ → ℝ := fun index =>
    slope * ((if denseDigits blockLength (fun index => (digits index).1) index then (1 : ℝ) else 0) * ratio ^ index) +
      (if denseDigits blockLength (fun index => (digits index).2) index then (1 : ℝ) else 0) * ratio ^ index
  have hsum : Summable term :=
    ((address_summable hpositive hlt (denseDigits blockLength (fun index => (digits index).1))).mul_left slope).add
      (address_summable hpositive hlt (denseDigits blockLength (fun index => (digits index).2)))
  have hsupport : Function.support term ⊆ Set.range
      (fun position : ℕ × Fin (blockLength - 1) => blockLength * position.1 + position.2.val + 1) := by
    intro index hindex
    apply denseBlockIndex_range hblock
    intro hmod
    exact hindex (by simp [term, denseDigits, hmod])
  have hsample := (denseBlockIndex_injective blockLength).tsum_eq hsupport
  have hrearrange := (hsum.comp_injective (denseBlockIndex_injective blockLength)).tsum_prod
  simp only [Function.comp_apply] at hrearrange
  have hprojection : denseProjection ratio slope blockLength digits = (1 - ratio) * ∑' index, term index := by
    unfold denseProjection address
    dsimp only [term]
    rw [Summable.tsum_add
      ((address_summable hpositive hlt (denseDigits blockLength (fun index => (digits index).1))).mul_left slope)
      (address_summable hpositive hlt (denseDigits blockLength (fun index => (digits index).2)))]
    rw [tsum_mul_left]
    ring
  rw [hprojection, ← hsample, hrearrange, ← tsum_mul_left]
  apply tsum_congr
  intro block
  rw [tsum_fintype]
  unfold denseBlockTranslation
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro offset hoffset
  have hoffset : offset.val + 1 < blockLength := by omega
  have hmod : (blockLength * block + offset.val + 1) % blockLength ≠ 0 := by
    have heq : (blockLength * block + offset.val + 1) % blockLength = offset.val + 1 := by
      rw [Nat.add_assoc, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
      exact Nat.mod_eq_of_lt hoffset
    rw [heq]
    omega
  have hpower : ratio ^ (blockLength * block + offset.val + 1) =
      (ratio ^ blockLength) ^ block * ratio ^ (offset.val + 1) := by
    rw [Nat.add_assoc, pow_add, pow_mul]
  simp only [term, denseDigits, hmod, if_false, denseBlockCoding, hpower]
  ring

end LambdaCantor.First.LinearRegularity



