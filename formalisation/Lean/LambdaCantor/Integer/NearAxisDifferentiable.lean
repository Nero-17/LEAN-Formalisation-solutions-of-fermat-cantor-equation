import LambdaCantor.Integer.NearAxisLog
import Mathlib.Analysis.Calculus.FDeriv.Prod

namespace LambdaCantor.Integer

theorem nearAxisLog_hasFDerivAt (n d p q : ℕ) (P Q scale x y : ℝ)
    (positiveU : 0 < P+x)
    (positiveResidual : 0 < ((Q+1-y)/3^q)*fermatQuotient n (scale*((Q+1-y)/3^q))) :
    ∃ derivative : (ℝ × ℝ) →L[ℝ] ℝ,
      HasFDerivAt (fun point : ℝ × ℝ => nearAxisLog n d p q P Q scale point.1 point.2)
        derivative (x,y) ∧
      ∀ direction, derivative direction = nearAxisHorizontal n P x*direction.1+
        nearAxisVertical n q Q scale y*direction.2 := by
  have first := (hasDerivAt_nearAxisHorizontal n d p q P Q scale x 0 positiveU).hasFDerivAt.comp
    (x,y) (hasFDerivAt_fst : HasFDerivAt (fun point : ℝ × ℝ => point.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (x,y))
  have second := (hasDerivAt_nearAxisVertical n d p q P Q scale 0 y positiveResidual).hasFDerivAt.comp
    (x,y) (hasFDerivAt_snd : HasFDerivAt (fun point : ℝ × ℝ => point.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (x,y))
  have combined := (first.add second).sub_const (nearAxisLog n d p q P Q scale 0 0)
  have identity : (fun point : ℝ × ℝ =>
      nearAxisLog n d p q P Q scale point.1 0+
        nearAxisLog n d p q P Q scale 0 point.2-nearAxisLog n d p q P Q scale 0 0) =
      (fun point : ℝ × ℝ => nearAxisLog n d p q P Q scale point.1 point.2) := by
    funext point
    unfold nearAxisLog
    ring
  simp only [Pi.add_apply,Function.comp_apply] at combined
  rw [identity] at combined
  refine ⟨(ContinuousLinearMap.toSpanSingleton ℝ (nearAxisHorizontal n P x)).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ)+
    (ContinuousLinearMap.toSpanSingleton ℝ (nearAxisVertical n q Q scale y)).comp
      (ContinuousLinearMap.snd ℝ ℝ ℝ),combined,?_⟩
  intro direction
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',smul_eq_mul]
  ring

end LambdaCantor.Integer
