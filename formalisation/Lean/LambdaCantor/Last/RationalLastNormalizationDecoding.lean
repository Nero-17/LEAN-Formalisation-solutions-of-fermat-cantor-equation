import LambdaCantor.Last.RationalLastNormalizationGeometry

noncomputable section
namespace LambdaCantor.Last

/-- Prefix decoding is proved on the actual canonical Cantor set. A point
of the unit interval whose prefix image is Cantor is itself Cantor. -/
theorem scalarWordMap_reflects_cantorSet {ratio coordinate : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2) (word : List Bool)
    (bounds : coordinate ∈ Set.Icc (0 : ℝ) 1)
    (membership : scalarWordMap ratio word coordinate ∈ cantorSet ratio) :
    coordinate ∈ cantorSet ratio := by
  have less_one : ratio < 1 := by linarith
  induction word with
  | nil => exact membership
  | cons digit rest induction =>
    have tail_bounds := scalarWordMap_bounds positive.le less_one rest bounds
    rw [scalarWordMap, cantorSet_selfsimilar positive.le less_one] at membership
    cases digit
    · simp only [Bool.false_eq_true, if_false, zero_add] at membership
      rcases membership with ⟨tail, tail_mem, representation⟩ | ⟨tail, tail_mem, representation⟩
      · apply induction
        have equal : tail = scalarWordMap ratio rest coordinate :=
          mul_left_cancel₀ positive.ne' representation
        simpa only [← equal] using tail_mem
      · have original_bounds := cantorSet_subset_unitInterval positive.le less_one tail_mem
        exfalso
        nlinarith [mul_nonneg positive.le original_bounds.1,
          mul_le_mul_of_nonneg_left tail_bounds.2 positive.le]
    · simp only [if_true] at membership
      rcases membership with ⟨tail, tail_mem, representation⟩ | ⟨tail, tail_mem, representation⟩
      · have original_bounds := cantorSet_subset_unitInterval positive.le less_one tail_mem
        exfalso
        nlinarith [mul_le_mul_of_nonneg_left original_bounds.2 positive.le,
          mul_nonneg positive.le tail_bounds.1]
      · apply induction
        have equal : tail = scalarWordMap ratio rest coordinate :=
          mul_left_cancel₀ positive.ne' (add_left_cancel representation)
        simpa only [← equal] using tail_mem

def anisotropicPrefixInverse (ratio : ℝ) (firstWord secondWord : List Bool)
    (point : ℝ × ℝ) : ℝ × ℝ :=
  ((point.1-scalarWordMap ratio firstWord 0)/ratio^firstWord.length,
    (point.2-scalarWordMap ratio secondWord 0)/ratio^secondWord.length)

theorem continuous_anisotropicPrefixInverse (ratio : ℝ) (firstWord secondWord : List Bool) :
    Continuous (anisotropicPrefixInverse ratio firstWord secondWord) := by
  unfold anisotropicPrefixInverse
  fun_prop

theorem anisotropicPrefixMap_inverse {ratio : ℝ} (positive : 0 < ratio)
    (firstWord secondWord : List Bool) (point : ℝ × ℝ) :
    anisotropicPrefixMap ratio firstWord secondWord
      (anisotropicPrefixInverse ratio firstWord secondWord point) = point := by
  apply Prod.ext <;>
    simp only [anisotropicPrefixMap, anisotropicPrefixInverse] <;>
    rw [scalarWordMap_affine] <;>
    field_simp [(pow_pos positive firstWord.length).ne', (pow_pos positive secondWord.length).ne'] <;>
    ring

theorem anisotropicPrefixInverse_map {ratio : ℝ} (positive : 0 < ratio)
    (firstWord secondWord : List Bool) (point : ℝ × ℝ) :
    anisotropicPrefixInverse ratio firstWord secondWord
      (anisotropicPrefixMap ratio firstWord secondWord point) = point := by
  apply (anisotropicPrefixMap_antilipschitz positive firstWord secondWord).injective
  rw [anisotropicPrefixMap_inverse positive]

/-- Actual dust inside a prefix rectangle decodes to actual dust. This is
the inverse membership needed to transport nearby perfect-fibre points. -/
theorem anisotropicPrefixInverse_mem_dust_of_hull {ratio : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2) (firstWord secondWord : List Bool)
    {point : ℝ × ℝ} (membership : point ∈ cantorDust ratio)
    (first_bounds : point.1 ∈ Set.Icc (scalarWordMap ratio firstWord 0) (scalarWordMap ratio firstWord 1))
    (second_bounds : point.2 ∈ Set.Icc (scalarWordMap ratio secondWord 0) (scalarWordMap ratio secondWord 1)) :
    anisotropicPrefixInverse ratio firstWord secondWord point ∈ cantorDust ratio := by
  have first_unit : (point.1-scalarWordMap ratio firstWord 0)/ratio^firstWord.length ∈
      Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr first_bounds.1) (pow_nonneg positive.le _)
    · apply (div_le_one (pow_pos positive _)).mpr
      rw [scalarWordMap_affine ratio firstWord 1] at first_bounds
      linarith [first_bounds.2]
  have second_unit : (point.2-scalarWordMap ratio secondWord 0)/ratio^secondWord.length ∈
      Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr second_bounds.1) (pow_nonneg positive.le _)
    · apply (div_le_one (pow_pos positive _)).mpr
      rw [scalarWordMap_affine ratio secondWord 1] at second_bounds
      linarith [second_bounds.2]
  have mapped := anisotropicPrefixMap_inverse positive firstWord secondWord point
  constructor
  · apply scalarWordMap_reflects_cantorSet positive less_half firstWord first_unit
    have equal := congrArg Prod.fst mapped
    change scalarWordMap ratio firstWord
      ((point.1-scalarWordMap ratio firstWord 0)/ratio^firstWord.length) = point.1 at equal
    rw [equal]
    exact membership.1
  · apply scalarWordMap_reflects_cantorSet positive less_half secondWord second_unit
    have equal := congrArg Prod.snd mapped
    change scalarWordMap ratio secondWord
      ((point.2-scalarWordMap ratio secondWord 0)/ratio^secondWord.length) = point.2 at equal
    rw [equal]
    exact membership.2

end LambdaCantor.Last
