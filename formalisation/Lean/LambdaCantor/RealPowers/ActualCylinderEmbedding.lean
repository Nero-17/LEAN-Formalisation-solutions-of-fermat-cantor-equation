import LambdaCantor.Last.AffineRectangleEmbedding
import LambdaCantor.Last.NormalizedCylinder
import LambdaCantor.Last.ReturnWords

-- Generic actual-cylinder embedding, copied from Last.IrrationalEmbedding.
-- ReturnWords supplies the canonical cantorDust type; its scaling lemmas
-- are already in AffineRectangleEmbedding.
noncomputable section
namespace LambdaCantor.RealPowers
open Last

def nearAxisCylinderEmbedding (ratio : ℝ) (firstDepth secondDepth : ℕ)
    (firstWord secondWord : List Bool) (point : ℝ × ℝ) : ℝ × ℝ :=
  (ratio^firstDepth*scalarWordMap ratio firstWord point.1,
    1-ratio^secondDepth*scalarWordMap ratio secondWord (1-point.2))

theorem nearAxisCylinderEmbedding_mem_dust {ratio : ℝ}
    (positive : 0 < ratio) (less_one : ratio < 1)
    (firstDepth secondDepth : ℕ) (firstWord secondWord : List Bool)
    {point : ℝ × ℝ} (membership : point ∈ cantorDust ratio) :
    nearAxisCylinderEmbedding ratio firstDepth secondDepth firstWord secondWord point ∈ cantorDust ratio := by
  constructor
  · exact cantor_power_scale_mem positive.le less_one firstDepth
      (scalarWordMap_mem_cantorSet positive.le less_one firstWord membership.1)
  · exact one_sub_mem_cantorSet positive.le less_one
      (cantor_power_scale_mem positive.le less_one secondDepth
        (scalarWordMap_mem_cantorSet positive.le less_one secondWord
          (one_sub_mem_cantorSet positive.le less_one membership.2)))

theorem nearAxisCylinderEmbedding_eq_affine (ratio : ℝ)
    (firstDepth secondDepth : ℕ) (firstWord secondWord : List Bool) :
    nearAxisCylinderEmbedding ratio firstDepth secondDepth firstWord secondWord =
      affineRectangleEmbedding
        (ratio^firstDepth*scalarWordMap ratio firstWord 0) (ratio^firstDepth*ratio^firstWord.length)
        (1-ratio^secondDepth*scalarWordMap ratio secondWord 1) (ratio^secondDepth*ratio^secondWord.length) := by
  funext point
  apply Prod.ext <;> simp only [nearAxisCylinderEmbedding, affineRectangleEmbedding]
  · rw [scalarWordMap_affine]
    ring
  · rw [scalarWordMap_affine ratio secondWord (1-point.2), scalarWordMap_affine ratio secondWord 1]
    ring

theorem nearAxisCylinderEmbedding_zero_mem_intersection {ratio exponent : ℝ}
    (positive : 0 < ratio) (less_one : ratio < 1) (exponent_positive : 0 < exponent)
    (firstDepth secondDepth : ℕ) (firstWord secondWord : List Bool)
    {point : ℝ × ℝ} (membership : point ∈ cantorDust ratio)
    (zero_source : normalizedCylinderSource exponent
      (exponent*ratio^secondDepth/(ratio^firstDepth)^exponent) (ratio^secondDepth)
      (scalarWordMap ratio firstWord 0) (ratio^firstWord.length)
      (scalarWordMap ratio secondWord 1) (ratio^secondWord.length) point = 0) :
    nearAxisCylinderEmbedding ratio firstDepth secondDepth firstWord secondWord point ∈ intersection exponent ratio := by
  have dust_mem := nearAxisCylinderEmbedding_mem_dust positive less_one firstDepth secondDepth firstWord secondWord membership
  refine ⟨dust_mem.1, dust_mem.2, ?_⟩
  have first_nonnegative := (scalarWordMap_bounds positive.le less_one firstWord
    (cantorSet_subset_unitInterval positive.le less_one membership.1)).1
  have denominator_positive := Real.rpow_pos_of_pos (pow_pos positive firstDepth) exponent
  have second_scale_positive := pow_pos positive secondDepth
  have first_eq : scalarWordMap ratio firstWord 0+ratio^firstWord.length*point.1 =
      scalarWordMap ratio firstWord point.1 := (scalarWordMap_affine ratio firstWord point.1).symm
  have second_eq : 1-ratio^secondDepth*scalarWordMap ratio secondWord 1+
      ratio^secondDepth*ratio^secondWord.length*point.2 =
      1-ratio^secondDepth*scalarWordMap ratio secondWord (1-point.2) := by
    rw [scalarWordMap_affine ratio secondWord 1, scalarWordMap_affine ratio secondWord (1-point.2)]
    ring
  unfold normalizedCylinderSource at zero_source
  rw [first_eq, second_eq] at zero_source
  have factor : (exponent*ratio^secondDepth/(ratio^firstDepth)^exponent)/(exponent*ratio^secondDepth) =
      1/(ratio^firstDepth)^exponent := by
    field_simp [exponent_positive.ne', second_scale_positive.ne', denominator_positive.ne']
  rw [factor] at zero_source
  change (ratio^firstDepth*scalarWordMap ratio firstWord point.1)^exponent+
    (1-ratio^secondDepth*scalarWordMap ratio secondWord (1-point.2))^exponent = 1
  rw [Real.mul_rpow (pow_pos positive firstDepth).le first_nonnegative]
  have multiplied := congrArg (fun value => (ratio^firstDepth)^exponent*value) zero_source
  simp only [mul_add, mul_zero] at multiplied
  field_simp [denominator_positive.ne'] at multiplied
  nlinarith

/-- Positive dimension of an actual normalized cylinder source transfers to
the original Fermat intersection. -/
theorem positive_dimension_of_nearAxisCylinderSource {ratio exponent : ℝ}
    (positive : 0 < ratio) (less_one : ratio < 1) (exponent_positive : 0 < exponent)
    (firstDepth secondDepth : ℕ) (firstWord secondWord : List Bool)
    (source_positive : 0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧
      normalizedCylinderSource exponent
        (exponent*ratio^secondDepth/(ratio^firstDepth)^exponent) (ratio^secondDepth)
        (scalarWordMap ratio firstWord 0) (ratio^firstWord.length)
        (scalarWordMap ratio secondWord 1) (ratio^secondWord.length) point = 0}) :
    0 < dimH (intersection exponent ratio) := by
  have embedding_bound := affineRectangleEmbedding_antilipschitz
    (mul_pos (pow_pos positive firstDepth) (pow_pos positive firstWord.length))
    (mul_pos (pow_pos positive secondDepth) (pow_pos positive secondWord.length))
    (ratio^firstDepth*scalarWordMap ratio firstWord 0)
    (1-ratio^secondDepth*scalarWordMap ratio secondWord 1)
  rw [← nearAxisCylinderEmbedding_eq_affine] at embedding_bound
  apply source_positive.trans_le (embedding_bound.le_dimH_image _ |>.trans (dimH_mono ?_))
  rintro point ⟨source, source_mem, rfl⟩
  exact nearAxisCylinderEmbedding_zero_mem_intersection positive less_one exponent_positive
    firstDepth secondDepth firstWord secondWord source_mem.1 source_mem.2

end LambdaCantor.RealPowers


