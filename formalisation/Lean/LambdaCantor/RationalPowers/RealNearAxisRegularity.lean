import LambdaCantor.RationalPowers.RealNearAxisUniform
import LambdaCantor.Classical.DerivativeLocalization
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
namespace LambdaCantor.RationalPowers

/-- The exact logarithmic source is strictly differentiable for every real
exponent at least one on its positive rectangle. No integer polynomial
identity is used. -/
theorem realNearAxisLog_hasStrictFDerivAt {exponent phase scale : ℝ}
    (exponent_ge_one : 1 ≤ exponent) (scale_nonzero : scale ≠ 0)
    (horizontalDepth verticalDepth : ℕ) (horizontal vertical x y : ℝ)
    (horizontal_positive : 0 < horizontal+x)
    (drop_positive : 0 < realPowerDrop exponent scale ((vertical+1-y)/3^verticalDepth)) :
    ∃ derivative : (ℝ × ℝ) →L[ℝ] ℝ,
      HasStrictFDerivAt (fun point : ℝ × ℝ =>
        realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical scale point.1 point.2)
        derivative (x,y) ∧
      ∀ direction, derivative direction =
        (exponent/(horizontal+x))*direction.1+
          realNearAxisVertical exponent vertical scale y verticalDepth*direction.2 := by
  have coordinate_positive : 0 < (horizontal+x)/(3 : ℝ)^horizontalDepth := by positivity
  have horizontal_derivative := (((((hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (x,y))).const_add
    horizontal).mul_const (((3 : ℝ)^horizontalDepth)⁻¹)).log
      (by simpa only [div_eq_mul_inv] using coordinate_positive.ne')).const_mul exponent).const_add
        (phase*Real.log 3)
  have vertical_coordinate := ((hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (x,y))).const_sub
    (vertical+1)).mul_const (((3 : ℝ)^verticalDepth)⁻¹)
  have vertical_derivative := (((((vertical_coordinate.const_mul scale).const_sub 1).rpow_const
    (p := exponent) (Or.inr exponent_ge_one)).const_sub 1).mul_const scale⁻¹).log
      (by simpa only [realPowerDrop, div_eq_mul_inv] using drop_positive.ne')
  have combined := horizontal_derivative.sub vertical_derivative
  refine ⟨exponent • ((horizontal+x)/(3 : ℝ)^horizontalDepth)⁻¹ •
      ((3 : ℝ)^horizontalDepth)⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ -
    (realPowerDrop exponent scale ((vertical+1-y)/(3 : ℝ)^verticalDepth))⁻¹ •
      scale⁻¹ • -((exponent*(1-scale*((vertical+1-y)/(3 : ℝ)^verticalDepth))^(exponent-1)) •
        -(scale • ((3 : ℝ)^verticalDepth)⁻¹ • -ContinuousLinearMap.snd ℝ ℝ ℝ)), ?_, ?_⟩
  · have combined_little := HasFDerivAtFilter.isLittleOTVS combined
    apply HasFDerivAtFilter.of_isLittleOTVS
    have product_topology :
        (inferInstance : PseudoMetricSpace (ℝ × ℝ)).toUniformSpace.toTopologicalSpace =
          (instTopologicalSpaceProd : TopologicalSpace (ℝ × ℝ)) := by
      with_reducible_and_instances exact toTopologicalSpace_prod
    simpa only [product_topology, Pi.sub_apply, realNearAxisLog, realPowerDrop, div_eq_mul_inv,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul] using
        combined_little
  · intro direction
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
      realNearAxisVertical]
    field_simp [horizontal_positive.ne', scale_nonzero, drop_positive.ne']
    <;> ring

theorem continuousOn_realNearAxisLog {exponent phase scale : ℝ}
    (exponent_ge_one : 1 ≤ exponent) (scale_nonzero : scale ≠ 0)
    (horizontalDepth verticalDepth : ℕ) (horizontal vertical : ℝ)
    (horizontal_positive : 0 < horizontal)
    (drop_positive : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < realPowerDrop exponent scale ((vertical+1-y)/3^verticalDepth)) :
    ContinuousOn (fun point : ℝ × ℝ =>
      realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical scale point.1 point.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  intro point point_bounds
  obtain ⟨derivative, strict, formula⟩ := realNearAxisLog_hasStrictFDerivAt exponent_ge_one scale_nonzero
    horizontalDepth verticalDepth horizontal vertical point.1 point.2
    (by linarith [point_bounds.1.1]) (drop_positive _ point_bounds.2)
  exact strict.continuousAt.continuousWithinAt

theorem realNearAxisHorizontal_bounds (exponent horizontal coordinate : ℝ)
    (exponent_positive : 0 < exponent) (horizontal_positive : 0 < horizontal)
    (coordinate_bounds : coordinate ∈ Set.Icc (0 : ℝ) 1) :
    exponent/(horizontal+1) ≤ exponent/(horizontal+coordinate) ∧
      exponent/(horizontal+coordinate) ≤ exponent/horizontal := by
  constructor
  · exact div_le_div_of_nonneg_left exponent_positive.le (by linarith [coordinate_bounds.1])
      (by linarith [coordinate_bounds.2])
  · exact div_le_div_of_nonneg_left exponent_positive.le horizontal_positive
      (by linarith [coordinate_bounds.1])

end LambdaCantor.RationalPowers

