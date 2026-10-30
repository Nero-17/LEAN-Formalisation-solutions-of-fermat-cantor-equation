import LambdaCantor.Last.TwoBandReciprocal
import LambdaCantor.Last.AffineRectangleEmbedding
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
namespace LambdaCantor.Last

theorem actual_rectangle_derivative_ratio_identity
    {exponent ratio first second : ℝ}
    (hexponent : 0 < exponent) (hpositive : 0 < ratio)
    (hfirst : 0 < first) (hsecond : 0 < second) (firstDepth secondDepth : ℕ) :
    (exponent * ratio ^ secondDepth * second ^ (exponent - 1)) /
      (exponent * ratio ^ firstDepth * first ^ (exponent - 1)) =
      ratio ^ ((secondDepth : ℝ) - firstDepth) * (second / first) ^ (exponent - 1) := by
  rw [Real.rpow_sub hpositive, Real.rpow_natCast, Real.rpow_natCast,
    Real.div_rpow hsecond.le hfirst.le]
  field_simp [hexponent.ne', (pow_pos hpositive firstDepth).ne',
    (Real.rpow_pos_of_pos hfirst (exponent - 1)).ne']
  <;> ring

/-- The actual-rectangle paragraph of Section 4: positive canonical cylinder
hulls with strict Fermat corner inequalities and either orientation of the
exact derivative-ratio interval give positive-dimensional actual intersection.
No ambient C1 hypothesis for real powers is assumed. -/
theorem actual_rectangle_positive_dimension {exponent ratio : ℝ}
    (hexponent : 1 < exponent) (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (firstWord secondWord : List Bool)
    (hfirst : 0 < scalarWordMap ratio firstWord 0)
    (hsecond : 0 < scalarWordMap ratio secondWord 0)
    (hlowerCorner : (scalarWordMap ratio firstWord 0) ^ exponent +
      (scalarWordMap ratio secondWord 0) ^ exponent < 1)
    (hupperCorner : 1 < (scalarWordMap ratio firstWord 1) ^ exponent +
      (scalarWordMap ratio secondWord 1) ^ exponent)
    (bands :
      TwoBandInterval ratio
        (ratio ^ ((secondWord.length : ℝ) - firstWord.length) *
          (scalarWordMap ratio secondWord 0 / scalarWordMap ratio firstWord 1) ^ (exponent - 1))
        (ratio ^ ((secondWord.length : ℝ) - firstWord.length) *
          (scalarWordMap ratio secondWord 1 / scalarWordMap ratio firstWord 0) ^ (exponent - 1)) ∨
      TwoBandInterval ratio
        (1 / (ratio ^ ((secondWord.length : ℝ) - firstWord.length) *
          (scalarWordMap ratio secondWord 1 / scalarWordMap ratio firstWord 0) ^ (exponent - 1)))
        (1 / (ratio ^ ((secondWord.length : ℝ) - firstWord.length) *
          (scalarWordMap ratio secondWord 0 / scalarWordMap ratio firstWord 1) ^ (exponent - 1)))) :
    0 < dimH (intersection exponent ratio) := by
  have hless : ratio < 1 := by linarith
  have hexponentPositive : 0 < exponent := by linarith
  let firstLeft := scalarWordMap ratio firstWord 0
  let firstRight := scalarWordMap ratio firstWord 1
  let secondLeft := scalarWordMap ratio secondWord 0
  let secondRight := scalarWordMap ratio secondWord 1
  let firstScale := ratio ^ firstWord.length
  let secondScale := ratio ^ secondWord.length
  have hfirstScale : 0 < firstScale := pow_pos hpositive _
  have hsecondScale : 0 < secondScale := pow_pos hpositive _
  have hfirstEndpoint : firstLeft + firstScale = firstRight := by
    simpa only [firstLeft, firstScale, firstRight, mul_one] using
      (scalarWordMap_affine ratio firstWord 1).symm
  have hsecondEndpoint : secondLeft + secondScale = secondRight := by
    simpa only [secondLeft, secondScale, secondRight, mul_one] using
      (scalarWordMap_affine ratio secondWord 1).symm
  have hfirstOrder : firstLeft ≤ firstRight := by linarith
  have hsecondOrder : secondLeft ≤ secondRight := by linarith
  have hfirstRight : 0 < firstRight := hfirst.trans_le hfirstOrder
  have hsecondRight : 0 < secondRight := hsecond.trans_le hsecondOrder
  let lowerS := exponent * firstScale * firstLeft ^ (exponent - 1)
  let upperS := exponent * firstScale * firstRight ^ (exponent - 1)
  let lowerT := exponent * secondScale * secondLeft ^ (exponent - 1)
  let upperT := exponent * secondScale * secondRight ^ (exponent - 1)
  have hlowerS : 0 < lowerS :=
    mul_pos (mul_pos hexponentPositive hfirstScale) (Real.rpow_pos_of_pos hfirst _)
  have hlowerT : 0 < lowerT :=
    mul_pos (mul_pos hexponentPositive hsecondScale) (Real.rpow_pos_of_pos hsecond _)
  have horderS : lowerS ≤ upperS :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hfirst.le hfirstOrder (by linarith))
      (mul_pos hexponentPositive hfirstScale).le
  have horderT : lowerT ≤ upperT :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hsecond.le hsecondOrder (by linarith))
      (mul_pos hexponentPositive hsecondScale).le
  have hlowerRatio : lowerT / upperS =
      ratio ^ ((secondWord.length : ℝ) - firstWord.length) *
        (scalarWordMap ratio secondWord 0 / scalarWordMap ratio firstWord 1) ^ (exponent - 1) :=
    actual_rectangle_derivative_ratio_identity hexponentPositive hpositive hfirstRight hsecond
      firstWord.length secondWord.length
  have hupperRatio : upperT / lowerS =
      ratio ^ ((secondWord.length : ℝ) - firstWord.length) *
        (scalarWordMap ratio secondWord 1 / scalarWordMap ratio firstWord 0) ^ (exponent - 1) :=
    actual_rectangle_derivative_ratio_identity hexponentPositive hpositive hfirst hsecondRight
      firstWord.length secondWord.length
  have hderivativeBands : TwoBandInterval ratio (lowerT / upperS) (upperT / lowerS) ∨
      TwoBandInterval ratio (lowerS / upperT) (upperS / lowerT) := by
    rw [← hlowerRatio, ← hupperRatio] at bands
    rcases bands with direct | reciprocal
    · exact Or.inl direct
    · exact Or.inr (by
        simpa only [one_div, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_comm, one_mul] using reciprocal)
  let function : (ℝ × ℝ) → ℝ := fun point =>
    (firstLeft + firstScale * point.1) ^ exponent +
      (secondLeft + secondScale * point.2) ^ exponent
  let derivativeS : (ℝ × ℝ) → ℝ := fun point =>
    exponent * firstScale * (firstLeft + firstScale * point.1) ^ (exponent - 1)
  let derivativeT : (ℝ × ℝ) → ℝ := fun point =>
    exponent * secondScale * (secondLeft + secondScale * point.2) ^ (exponent - 1)
  have hcontinuous : Continuous function := by
    exact ((continuous_const.add (continuous_const.mul continuous_fst)).rpow_const
      (fun _ => Or.inr hexponentPositive.le)).add
      ((continuous_const.add (continuous_const.mul continuous_snd)).rpow_const
        (fun _ => Or.inr hexponentPositive.le))
  have hfirstBounds : ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
      firstLeft ≤ firstLeft + firstScale * coordinate ∧
        firstLeft + firstScale * coordinate ≤ firstRight := by
    intro coordinate hcoordinate
    constructor <;> nlinarith [mul_nonneg hfirstScale.le hcoordinate.1,
      mul_le_mul_of_nonneg_left hcoordinate.2 hfirstScale.le]
  have hsecondBounds : ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
      secondLeft ≤ secondLeft + secondScale * coordinate ∧
        secondLeft + secondScale * coordinate ≤ secondRight := by
    intro coordinate hcoordinate
    constructor <;> nlinarith [mul_nonneg hsecondScale.le hcoordinate.1,
      mul_le_mul_of_nonneg_left hcoordinate.2 hsecondScale.le]
  have hstrict : ∀ point : ℝ × ℝ, point.1 ∈ Set.Icc (0 : ℝ) 1 →
      point.2 ∈ Set.Icc (0 : ℝ) 1 → HasStrictFDerivAt function
        (derivativeS point • ContinuousLinearMap.fst ℝ ℝ ℝ +
          derivativeT point • ContinuousLinearMap.snd ℝ ℝ ℝ) point := by
    intro point hwidth hheight
    have hfirstAffine := ((hasStrictFDerivAt_fst (𝕜 := ℝ) (p := point)).const_mul firstScale).const_add firstLeft
    have hsecondAffine := ((hasStrictFDerivAt_snd (𝕜 := ℝ) (p := point)).const_mul secondScale).const_add secondLeft
    have hfirstPower := hfirstAffine.rpow_const (p := exponent)
      (Or.inl (hfirst.trans_le (hfirstBounds point.1 hwidth).1).ne')
    have hsecondPower := hsecondAffine.rpow_const (p := exponent)
      (Or.inl (hsecond.trans_le (hsecondBounds point.2 hheight).1).ne')
    have hsum := hfirstPower.add hsecondPower
    simp only [smul_smul] at hsum
    have hfirstCoefficient : exponent * (firstLeft + firstScale * point.1) ^ (exponent - 1) * firstScale =
        exponent * firstScale * (firstLeft + firstScale * point.1) ^ (exponent - 1) := by ring
    have hsecondCoefficient : exponent * (secondLeft + secondScale * point.2) ^ (exponent - 1) * secondScale =
        exponent * secondScale * (secondLeft + secondScale * point.2) ^ (exponent - 1) := by ring
    rw [hfirstCoefficient, hsecondCoefficient] at hsum
    exact hsum
  have hboundS : ∀ point : ℝ × ℝ, point.1 ∈ Set.Icc (0 : ℝ) 1 →
      point.2 ∈ Set.Icc (0 : ℝ) 1 → lowerS ≤ derivativeS point ∧ derivativeS point ≤ upperS := by
    intro point hwidth hheight
    have hbounds := hfirstBounds point.1 hwidth
    exact ⟨mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hfirst.le hbounds.1 (by linarith))
        (mul_pos hexponentPositive hfirstScale).le,
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hfirst.le.trans hbounds.1) hbounds.2 (by linarith))
        (mul_pos hexponentPositive hfirstScale).le⟩
  have hboundT : ∀ point : ℝ × ℝ, point.1 ∈ Set.Icc (0 : ℝ) 1 →
      point.2 ∈ Set.Icc (0 : ℝ) 1 → lowerT ≤ derivativeT point ∧ derivativeT point ≤ upperT := by
    intro point hwidth hheight
    have hbounds := hsecondBounds point.2 hheight
    exact ⟨mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hsecond.le hbounds.1 (by linarith))
        (mul_pos hexponentPositive hsecondScale).le,
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hsecond.le.trans hbounds.1) hbounds.2 (by linarith))
        (mul_pos hexponentPositive hsecondScale).le⟩
  have hlevel : (1 : ℝ) ∈ Set.Ioo (function (0, 0)) (function (1, 1)) := by
    simpa only [Set.mem_Ioo, function, mul_zero, add_zero, mul_one, hfirstEndpoint, hsecondEndpoint] using
      (show firstLeft ^ exponent + secondLeft ^ exponent < 1 ∧
        1 < firstRight ^ exponent + secondRight ^ exponent from ⟨hlowerCorner, hupperCorner⟩)
  have hdimension : 0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧ function point = 1} := by
    rcases hderivativeBands with direct | reciprocal
    · exact two_band_positive_derivative_criterion function derivativeS derivativeT hcontinuous
        hpositive hhalf hlowerS horderS direct hstrict hboundS hboundT hlevel
    · exact two_band_positive_derivative_criterion_reciprocal function derivativeS derivativeT hcontinuous
        hpositive hhalf hlowerS horderS hlowerT horderT reciprocal hstrict hboundS hboundT hlevel
  have hembedding := affineRectangleEmbedding_antilipschitz hfirstScale hsecondScale firstLeft secondLeft
  apply hdimension.trans_le ((hembedding.le_dimH_image _).trans (dimH_mono ?_))
  rintro point ⟨value, hvalue, rfl⟩
  refine ⟨?_, ?_, hvalue.2⟩
  · change firstLeft + firstScale * value.1 ∈ cantorSet ratio
    simpa only [scalarWordMap_affine ratio firstWord value.1] using
      scalarWordMap_mem_cantorSet hpositive.le hless firstWord hvalue.1.1
  · change secondLeft + secondScale * value.2 ∈ cantorSet ratio
    simpa only [scalarWordMap_affine ratio secondWord value.2] using
      scalarWordMap_mem_cantorSet hpositive.le hless secondWord hvalue.1.2

#print axioms actual_rectangle_derivative_ratio_identity
#print axioms actual_rectangle_positive_dimension

end LambdaCantor.Last
