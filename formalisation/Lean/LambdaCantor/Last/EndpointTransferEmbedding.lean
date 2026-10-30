import LambdaCantor.Last.ScalarCylinders
import LambdaCantor.Last.NormalizedCylinder
import LambdaCantor.Last.ReturnWords

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

private def endpointAffineEmbedding (firstLeft firstScale secondLeft secondScale : ℝ)
    (point : ℝ × ℝ) : ℝ × ℝ :=
  (firstLeft + firstScale * point.1, secondLeft + secondScale * point.2)

private theorem endpointAffineEmbedding_antilipschitz {firstScale secondScale : ℝ}
    (hfirst : 0 < firstScale) (hsecond : 0 < secondScale) (firstLeft secondLeft : ℝ) :
    AntilipschitzWith
      (⟨max firstScale⁻¹ secondScale⁻¹, le_max_of_le_left (inv_nonneg.mpr hfirst.le)⟩ : ℝ≥0)
      (endpointAffineEmbedding firstLeft firstScale secondLeft secondScale) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro first second
  change dist first second ≤ max firstScale⁻¹ secondScale⁻¹ *
    dist (endpointAffineEmbedding firstLeft firstScale secondLeft secondScale first)
      (endpointAffineEmbedding firstLeft firstScale secondLeft secondScale second)
  have hfirst_distance : dist
      (endpointAffineEmbedding firstLeft firstScale secondLeft secondScale first).1
      (endpointAffineEmbedding firstLeft firstScale secondLeft secondScale second).1 =
      firstScale * dist first.1 second.1 := by
    simp only [endpointAffineEmbedding, dist_add_left, Real.dist_eq]
    rw [← mul_sub, abs_mul, abs_of_pos hfirst]
  have hsecond_distance : dist
      (endpointAffineEmbedding firstLeft firstScale secondLeft secondScale first).2
      (endpointAffineEmbedding firstLeft firstScale secondLeft secondScale second).2 =
      secondScale * dist first.2 second.2 := by
    simp only [endpointAffineEmbedding, dist_add_left, Real.dist_eq]
    rw [← mul_sub, abs_mul, abs_of_pos hsecond]
  rw [Prod.dist_eq, Prod.dist_eq, hfirst_distance, hsecond_distance]
  apply max_le
  · calc
      dist first.1 second.1 = firstScale⁻¹ * (firstScale * dist first.1 second.1) := by
        rw [← mul_assoc, inv_mul_cancel₀ hfirst.ne', one_mul]
      _ ≤ max firstScale⁻¹ secondScale⁻¹ * (firstScale * dist first.1 second.1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hfirst.le dist_nonneg)
      _ ≤ max firstScale⁻¹ secondScale⁻¹ *
          max (firstScale * dist first.1 second.1) (secondScale * dist first.2 second.2) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (le_max_of_le_left (inv_nonneg.mpr hfirst.le))
  · calc
      dist first.2 second.2 = secondScale⁻¹ * (secondScale * dist first.2 second.2) := by
        rw [← mul_assoc, inv_mul_cancel₀ hsecond.ne', one_mul]
      _ ≤ max firstScale⁻¹ secondScale⁻¹ * (secondScale * dist first.2 second.2) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hsecond.le dist_nonneg)
      _ ≤ max firstScale⁻¹ secondScale⁻¹ *
          max (firstScale * dist first.1 second.1) (secondScale * dist first.2 second.2) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (le_max_of_le_left (inv_nonneg.mpr hfirst.le))

private theorem endpoint_power_scale_mem {ratio coordinate : ℝ} (hpositive : 0 ≤ ratio)
    (hless : ratio < 1) (depth : ℕ) (hcoordinate : coordinate ∈ cantorSet ratio) :
    ratio ^ depth * coordinate ∈ cantorSet ratio := by
  induction depth with
  | zero => simpa using hcoordinate
  | succ depth ih =>
      simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using low_copy_mem hpositive hless ih

def endpointAxisEmbedding (ratio : ℝ) (firstDepth secondDepth : ℕ)
    (firstWord secondWord : List Bool) (point : ℝ × ℝ) : ℝ × ℝ :=
  (ratio ^ firstDepth * scalarWordMap ratio firstWord point.1,
    1 - ratio ^ secondDepth * scalarWordMap ratio secondWord (1 - point.2))

theorem endpointAxisEmbedding_mem_dust {ratio : ℝ}
    (hpositive : 0 < ratio) (hless : ratio < 1)
    (firstDepth secondDepth : ℕ) (firstWord secondWord : List Bool)
    {point : ℝ × ℝ} (hpoint : point ∈ cantorDust ratio) :
    endpointAxisEmbedding ratio firstDepth secondDepth firstWord secondWord point ∈ cantorDust ratio := by
  constructor
  · exact endpoint_power_scale_mem hpositive.le hless firstDepth
      (scalarWordMap_mem_cantorSet hpositive.le hless firstWord hpoint.1)
  · exact one_sub_mem_cantorSet hpositive.le hless
      (endpoint_power_scale_mem hpositive.le hless secondDepth
        (scalarWordMap_mem_cantorSet hpositive.le hless secondWord
          (one_sub_mem_cantorSet hpositive.le hless hpoint.2)))

private theorem endpointAxisEmbedding_eq_affine (ratio : ℝ)
    (firstDepth secondDepth : ℕ) (firstWord secondWord : List Bool) :
    endpointAxisEmbedding ratio firstDepth secondDepth firstWord secondWord =
      endpointAffineEmbedding
        (ratio ^ firstDepth * scalarWordMap ratio firstWord 0) (ratio ^ firstDepth * ratio ^ firstWord.length)
        (1 - ratio ^ secondDepth * scalarWordMap ratio secondWord 1) (ratio ^ secondDepth * ratio ^ secondWord.length) := by
  funext point
  apply Prod.ext <;> simp only [endpointAxisEmbedding, endpointAffineEmbedding]
  · rw [scalarWordMap_affine]
    ring
  · rw [scalarWordMap_affine ratio secondWord (1 - point.2), scalarWordMap_affine ratio secondWord 1]
    ring

theorem endpointAxisEmbedding_zero_mem_intersection {ratio exponent : ℝ}
    (hpositive : 0 < ratio) (hless : ratio < 1) (hexponent : 0 < exponent)
    (firstDepth secondDepth : ℕ) (firstWord secondWord : List Bool)
    {point : ℝ × ℝ} (hpoint : point ∈ cantorDust ratio)
    (hzero : normalizedCylinderSource exponent
      (exponent * ratio ^ secondDepth / (ratio ^ firstDepth) ^ exponent) (ratio ^ secondDepth)
      (scalarWordMap ratio firstWord 0) (ratio ^ firstWord.length)
      (scalarWordMap ratio secondWord 1) (ratio ^ secondWord.length) point = 0) :
    endpointAxisEmbedding ratio firstDepth secondDepth firstWord secondWord point ∈ intersection exponent ratio := by
  have hdust := endpointAxisEmbedding_mem_dust hpositive hless firstDepth secondDepth firstWord secondWord hpoint
  refine ⟨hdust.1, hdust.2, ?_⟩
  have hfirst_nonnegative := (scalarWordMap_bounds hpositive.le hless firstWord
    (cantorSet_subset_unitInterval hpositive.le hless hpoint.1)).1
  have hdenominator := Real.rpow_pos_of_pos (pow_pos hpositive firstDepth) exponent
  have hsecond_scale := pow_pos hpositive secondDepth
  have hfirst : scalarWordMap ratio firstWord 0 + ratio ^ firstWord.length * point.1 =
      scalarWordMap ratio firstWord point.1 := (scalarWordMap_affine ratio firstWord point.1).symm
  have hsecond : 1 - ratio ^ secondDepth * scalarWordMap ratio secondWord 1 +
      ratio ^ secondDepth * ratio ^ secondWord.length * point.2 =
      1 - ratio ^ secondDepth * scalarWordMap ratio secondWord (1 - point.2) := by
    rw [scalarWordMap_affine ratio secondWord 1, scalarWordMap_affine ratio secondWord (1 - point.2)]
    ring
  unfold normalizedCylinderSource at hzero
  rw [hfirst, hsecond] at hzero
  have hfactor : (exponent * ratio ^ secondDepth / (ratio ^ firstDepth) ^ exponent) /
      (exponent * ratio ^ secondDepth) = 1 / (ratio ^ firstDepth) ^ exponent := by
    field_simp [hexponent.ne', hsecond_scale.ne', hdenominator.ne']
  rw [hfactor] at hzero
  change (ratio ^ firstDepth * scalarWordMap ratio firstWord point.1) ^ exponent +
    (1 - ratio ^ secondDepth * scalarWordMap ratio secondWord (1 - point.2)) ^ exponent = 1
  rw [Real.mul_rpow (pow_pos hpositive firstDepth).le hfirst_nonnegative]
  have hmultiplied := congrArg (fun value => (ratio ^ firstDepth) ^ exponent * value) hzero
  simp only [mul_add, mul_zero] at hmultiplied
  field_simp [hdenominator.ne'] at hmultiplied
  nlinarith

/-- Minimal endpoint-embedding dimension transfer. No old irrational source,
thickness, orientation, or derivative-criterion module is imported. -/
theorem positive_dimension_of_endpointAxisSource {ratio exponent : ℝ}
    (hpositive : 0 < ratio) (hless : ratio < 1) (hexponent : 0 < exponent)
    (firstDepth secondDepth : ℕ) (firstWord secondWord : List Bool)
    (hsource : 0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧
      normalizedCylinderSource exponent
        (exponent * ratio ^ secondDepth / (ratio ^ firstDepth) ^ exponent) (ratio ^ secondDepth)
        (scalarWordMap ratio firstWord 0) (ratio ^ firstWord.length)
        (scalarWordMap ratio secondWord 1) (ratio ^ secondWord.length) point = 0}) :
    0 < dimH (intersection exponent ratio) := by
  have hbound := endpointAffineEmbedding_antilipschitz
    (mul_pos (pow_pos hpositive firstDepth) (pow_pos hpositive firstWord.length))
    (mul_pos (pow_pos hpositive secondDepth) (pow_pos hpositive secondWord.length))
    (ratio ^ firstDepth * scalarWordMap ratio firstWord 0)
    (1 - ratio ^ secondDepth * scalarWordMap ratio secondWord 1)
  rw [← endpointAxisEmbedding_eq_affine] at hbound
  apply hsource.trans_le (hbound.le_dimH_image _ |>.trans (dimH_mono ?_))
  rintro point ⟨source, hsource, rfl⟩
  exact endpointAxisEmbedding_zero_mem_intersection hpositive hless hexponent
    firstDepth secondDepth firstWord secondWord hsource.1 hsource.2

end LambdaCantor.Last
