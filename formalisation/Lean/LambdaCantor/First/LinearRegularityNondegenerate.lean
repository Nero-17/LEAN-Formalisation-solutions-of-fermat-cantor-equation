import LambdaCantor.First.LinearRegularityInvariant

noncomputable section
namespace LambdaCantor.First.LinearRegularity

/-- Insert arbitrary infinite dense blocks into the original paired address,
putting zero at each sparse position. -/
def denseBlockEmbedding (blockLength : ℕ) (words : ℕ → DenseBlock blockLength) : ℕ → Bool × Bool :=
  Function.extend
    (fun position : ℕ × Fin (blockLength - 1) => blockLength * position.1 + position.2.val + 1)
    (fun position => words position.1 position.2) (fun _ => (false, false))

theorem denseBlockCoding_embedding (blockLength : ℕ) (words : ℕ → DenseBlock blockLength) :
    denseBlockCoding blockLength (denseBlockEmbedding blockLength words) = words := by
  funext block offset
  simpa only [denseBlockCoding, denseBlockEmbedding] using
    (denseBlockIndex_injective blockLength).extend_apply
      (fun position : ℕ × Fin (blockLength - 1) => words position.1 position.2)
      (fun _ : ℕ => (false, false)) (block, offset)

theorem denseBlockEmbedding_injective (blockLength : ℕ) :
    Function.Injective (denseBlockEmbedding blockLength) := by
  intro left right hequal
  have h := congrArg (denseBlockCoding blockLength) hequal
  simpa only [denseBlockCoding_embedding] using h

theorem denseBlockEmbedding_sparse_zero (blockLength : ℕ) (words : ℕ → DenseBlock blockLength)
    (index : ℕ) (hmod : index % blockLength = 0) :
    denseBlockEmbedding blockLength words index = (false, false) := by
  apply Function.extend_apply'
  rintro ⟨position, hequal⟩
  have hoffset : position.2.val + 1 < blockLength := by omega
  have hresidue : (blockLength * position.1 + position.2.val + 1) % blockLength = position.2.val + 1 := by
    rw [Nat.add_assoc, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt hoffset
  rw [hequal, hmod] at hresidue
  omega

theorem denseProjection_embedding (ratio slope : ℝ) (blockLength : ℕ)
    (words : ℕ → DenseBlock blockLength) :
    denseProjection ratio slope blockLength (denseBlockEmbedding blockLength words) =
      pairedProjection ratio slope (denseBlockEmbedding blockLength words) := by
  have hleft : denseDigits blockLength (fun index => (denseBlockEmbedding blockLength words index).1) =
      fun index => (denseBlockEmbedding blockLength words index).1 := by
    funext index
    by_cases hmod : index % blockLength = 0
    · simp [denseDigits, hmod, denseBlockEmbedding_sparse_zero _ _ _ hmod]
    · simp [denseDigits, hmod]
  have hright : denseDigits blockLength (fun index => (denseBlockEmbedding blockLength words index).2) =
      fun index => (denseBlockEmbedding blockLength words index).2 := by
    funext index
    by_cases hmod : index % blockLength = 0
    · simp [denseDigits, hmod, denseBlockEmbedding_sparse_zero _ _ _ hmod]
    · simp [denseDigits, hmod]
  simp only [denseProjection, pairedProjection, hleft, hright]

/-- Infinite block-address nondegeneracy is inherited from actual Cantor
address injectivity, on every open slope interval. -/
theorem denseBlock_series_nondegenerate {ratio lowerSlope upperSlope : ℝ}
    (hratio : 0 < ratio) (hhalf : ratio < 1 / 2) (hslopes : lowerSlope < upperSlope)
    (blockLength : ℕ) (hblock : 0 < blockLength)
    (left right : ℕ → DenseBlock blockLength) (hne : left ≠ right) :
    ∃ slope ∈ Set.Ioo lowerSlope upperSlope,
      affineAddress (ratio ^ blockLength) (denseBlockTranslation blockLength (ratio, slope)) left ≠
      affineAddress (ratio ^ blockLength) (denseBlockTranslation blockLength (ratio, slope)) right := by
  have hpair :
      ((fun index => (denseBlockEmbedding blockLength left index).1),
        (fun index => (denseBlockEmbedding blockLength left index).2)) ≠
      ((fun index => (denseBlockEmbedding blockLength right index).1),
        (fun index => (denseBlockEmbedding blockLength right index).2)) := by
    intro hequal
    apply hne
    apply denseBlockEmbedding_injective blockLength
    funext index
    exact Prod.ext (congrFun (congrArg Prod.fst hequal) index) (congrFun (congrArg Prod.snd hequal) index)
  obtain ⟨slope, hslope, hdifferent⟩ := paired_address_projection_nondegenerate hratio hhalf hslopes _ _ hpair
  refine ⟨slope, hslope, ?_⟩
  have hleft := denseProjection_block_series hratio.le (lt_trans hhalf (by norm_num)) slope
    blockLength hblock (denseBlockEmbedding blockLength left)
  have hright := denseProjection_block_series hratio.le (lt_trans hhalf (by norm_num)) slope
    blockLength hblock (denseBlockEmbedding blockLength right)
  rw [denseProjection_embedding, denseBlockCoding_embedding] at hleft hright
  change pairedProjection ratio slope (denseBlockEmbedding blockLength left) ≠
    pairedProjection ratio slope (denseBlockEmbedding blockLength right) at hdifferent
  simpa only [affineAddress, hleft, hright] using hdifferent

end LambdaCantor.First.LinearRegularity
