import LambdaCantor.Integer.NearAxisRegularity
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace LambdaCantor.Integer

theorem contDiff_fermatQuotient (n : ℕ) : ContDiff ℝ 1 (fermatQuotient n) := by
  unfold fermatQuotient
  exact ContDiff.sum (fun i _ => (contDiff_const.sub contDiff_id).pow i)

/-- The rescaled logarithmic equation is genuinely C¹ at every point with
positive horizontal coordinate and positive residual, including scale zero. -/
theorem nearAxisLog_contDiffAt (n d p q : ℕ) (P Q scale x y : ℝ)
    (positiveU : 0 < P+x)
    (positiveResidual : 0 < ((Q+1-y)/3^q)*fermatQuotient n (scale*((Q+1-y)/3^q))) :
    ContDiffAt ℝ 1 (fun point : ℝ × ℝ => nearAxisLog n d p q P Q scale point.1 point.2) (x,y) := by
  have horizontal : ContDiff ℝ 1 (fun point : ℝ × ℝ => (P+point.1)/3^p) :=
    (contDiff_const.add contDiff_fst).div_const _
  have vertical : ContDiff ℝ 1 (fun point : ℝ × ℝ => (Q+1-point.2)/3^q) :=
    (contDiff_const.sub contDiff_snd).div_const _
  have residual : ContDiff ℝ 1 (fun point : ℝ × ℝ =>
      ((Q+1-point.2)/3^q)*fermatQuotient n (scale*((Q+1-point.2)/3^q))) :=
    vertical.mul ((contDiff_fermatQuotient n).comp (contDiff_const.mul vertical))
  have horizontalPositive : 0 < (P+x)/(3 : ℝ)^p := by positivity
  unfold nearAxisLog
  exact (contDiffAt_const.add (contDiffAt_const.mul
    ((horizontal.contDiffAt (x := (x,y))).log (ne_of_gt horizontalPositive)))).sub
      ((residual.contDiffAt (x := (x,y))).log (ne_of_gt positiveResidual))

theorem nearAxisLog_hasStrictFDerivAt (n d p q : ℕ) (P Q scale x y : ℝ)
    (positiveU : 0 < P+x)
    (positiveResidual : 0 < ((Q+1-y)/3^q)*fermatQuotient n (scale*((Q+1-y)/3^q))) :
    ∃ derivative : (ℝ × ℝ) →L[ℝ] ℝ,
      HasStrictFDerivAt (fun point : ℝ × ℝ => nearAxisLog n d p q P Q scale point.1 point.2)
        derivative (x,y) ∧
      ∀ direction, derivative direction = nearAxisHorizontal n P x*direction.1+
        nearAxisVertical n q Q scale y*direction.2 := by
  obtain ⟨derivative,differentiable,formula⟩ := nearAxisLog_hasFDerivAt
    n d p q P Q scale x y positiveU positiveResidual
  exact ⟨derivative,ContDiffAt.hasStrictFDerivAt'
    (nearAxisLog_contDiffAt n d p q P Q scale x y positiveU positiveResidual)
    differentiable (by norm_num),formula⟩

/-- Reciprocal good bands use the actual coordinate-swapped equation, whose
strict derivative swaps the two coefficients as required by the dimension bridge. -/
theorem nearAxisLog_swap_hasStrictFDerivAt (n d p q : ℕ) (P Q scale x y : ℝ)
    (positiveU : 0 < P+x)
    (positiveResidual : 0 < ((Q+1-y)/3^q)*fermatQuotient n (scale*((Q+1-y)/3^q))) :
    ∃ derivative : (ℝ × ℝ) →L[ℝ] ℝ,
      HasStrictFDerivAt (fun point : ℝ × ℝ => nearAxisLog n d p q P Q scale point.2 point.1)
        derivative (y,x) ∧
      ∀ direction, derivative direction = nearAxisVertical n q Q scale y*direction.1+
        nearAxisHorizontal n P x*direction.2 := by
  obtain ⟨derivative,strict,formula⟩ := nearAxisLog_hasStrictFDerivAt
    n d p q P Q scale x y positiveU positiveResidual
  have swapDerivative :=
    (hasStrictFDerivAt_snd : HasStrictFDerivAt (fun pair : ℝ × ℝ => pair.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (y,x)).prodMk
    (hasStrictFDerivAt_fst : HasStrictFDerivAt (fun pair : ℝ × ℝ => pair.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (y,x))
  have composed := strict.comp (y,x) swapDerivative
  refine ⟨derivative.comp
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)),?_,?_⟩
  · have composedLittle := HasFDerivAtFilter.isLittleOTVS composed
    apply HasFDerivAtFilter.of_isLittleOTVS
    have product_topology :
        (inferInstance : PseudoMetricSpace (ℝ × ℝ)).toUniformSpace.toTopologicalSpace =
          (instTopologicalSpaceProd : TopologicalSpace (ℝ × ℝ)) := by
      with_reducible_and_instances exact toTopologicalSpace_prod
    simpa only [product_topology,Function.comp_apply] using composedLittle
  · intro direction
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',formula]
    ring

end LambdaCantor.Integer
