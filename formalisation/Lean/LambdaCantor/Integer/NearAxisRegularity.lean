import LambdaCantor.Integer.NearAxisDifferentiable

namespace LambdaCantor.Integer

theorem continuousOn_nearAxisHorizontal (n : ℕ) (P : ℝ) (positiveP : 0 < P) :
    ContinuousOn (nearAxisHorizontal n P) (Set.Icc (0 : ℝ) 1) := by
  apply continuousOn_const.div (continuousOn_const.add continuousOn_id)
  intro x membership
  change P+x ≠ 0
  exact ne_of_gt (by linarith [membership.1])

theorem continuousOn_nearAxisVertical (n q : ℕ) (Q scale : ℝ)
    (positiveResidual : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < ((Q+1-y)/3^q)*fermatQuotient n (scale*((Q+1-y)/3^q))) :
    ContinuousOn (nearAxisVertical n q Q scale) (Set.Icc (0 : ℝ) 1) := by
  have numerator : Continuous (fun y : ℝ =>
      (n : ℝ)*(1-scale*((Q+1-y)/3^q))^(n-1)) :=
    continuous_const.mul ((continuous_const.sub
      (continuous_const.mul ((continuous_const.sub continuous_id).div_const _))).pow _)
  have denominator : Continuous (fun y : ℝ =>
      ((Q+1-y)/3^q)*fermatQuotient n (scale*((Q+1-y)/3^q))) :=
    (continuous_rescaled_fermat n).comp
      (continuous_const.prodMk ((continuous_const.sub continuous_id).div_const _))
  exact (numerator.continuousOn.div denominator.continuousOn
    (fun y hy => ne_of_gt (positiveResidual y hy))).div_const _

theorem nearAxis_derivatives_continuousAt (n q : ℕ) (P Q scale x y : ℝ)
    (positiveU : 0 < P+x)
    (positiveResidual : 0 < ((Q+1-y)/3^q)*fermatQuotient n (scale*((Q+1-y)/3^q))) :
    ContinuousAt (fun point : ℝ × ℝ => nearAxisHorizontal n P point.1) (x,y) ∧
    ContinuousAt (fun point : ℝ × ℝ => nearAxisVertical n q Q scale point.2) (x,y) := by
  constructor
  · exact continuousAt_const.div (continuousAt_const.add continuous_fst.continuousAt)
      (ne_of_gt positiveU)
  · have numerator : Continuous (fun point : ℝ × ℝ =>
        (n : ℝ)*(1-scale*((Q+1-point.2)/3^q))^(n-1)) :=
      continuous_const.mul ((continuous_const.sub
        (continuous_const.mul ((continuous_const.sub continuous_snd).div_const _))).pow _)
    have denominator : Continuous (fun point : ℝ × ℝ =>
        ((Q+1-point.2)/3^q)*fermatQuotient n (scale*((Q+1-point.2)/3^q))) :=
      (continuous_rescaled_fermat n).comp
        (continuous_const.prodMk ((continuous_const.sub continuous_snd).div_const _))
    exact (numerator.continuousAt.div denominator.continuousAt
      (ne_of_gt positiveResidual)).div_const _

end LambdaCantor.Integer
