import LambdaCantor.Integer.NearAxisUniform
import LambdaCantor.Classical.DerivativeLocalization

namespace LambdaCantor.Integer

noncomputable def nearAxisLog (n d p q : ℕ) (P Q scale x y : ℝ) : ℝ :=
  (d : ℝ)*Real.log 3+(n : ℝ)*Real.log ((P+x)/3^p)-
    Real.log (((Q+1-y)/3^q)*fermatQuotient n (scale*((Q+1-y)/3^q)))

noncomputable def nearAxisHorizontal (n : ℕ) (P x : ℝ) : ℝ := (n : ℝ)/(P+x)

noncomputable def nearAxisVertical (n q : ℕ) (Q scale y : ℝ) : ℝ :=
  fermatLogDerivative n scale ((Q+1-y)/3^q)/3^q

theorem nearAxisVertical_zero (n q : ℕ) (positive : 0 < n) (Q y : ℝ)
    (nonzero : Q+1-y ≠ 0) : nearAxisVertical n q Q 0 y = 1/(Q+1-y) := by
  unfold nearAxisVertical
  rw [fermatLogDerivative_zero n positive _ (div_ne_zero nonzero (by positivity))]
  field_simp [nonzero]

theorem hasDerivAt_nearAxisHorizontal (n d p q : ℕ) (P Q scale x y : ℝ)
    (positive : 0 < P+x) :
    HasDerivAt (fun t => nearAxisLog n d p q P Q scale t y)
      (nearAxisHorizontal n P x) x := by
  have argument := ((hasDerivAt_const x P).add (hasDerivAt_id x)).div_const ((3 : ℝ)^p)
  have logarithm := argument.log (show (P+x)/(3 : ℝ)^p ≠ 0 by positivity)
  have derivative := (logarithm.const_mul (n : ℝ)).const_add ((d : ℝ)*Real.log 3)
  have final := derivative.sub_const
    (Real.log (((Q+1-y)/3^q)*fermatQuotient n (scale*((Q+1-y)/3^q))))
  have derivativeIdentity : (n : ℝ)*((0+1)/(3 : ℝ)^p/((P+x)/(3 : ℝ)^p)) =
      nearAxisHorizontal n P x := by
    unfold nearAxisHorizontal
    simp only [zero_add]
    field_simp [ne_of_gt positive]
    <;> ring
  apply (final.congr_deriv derivativeIdentity).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t => by rfl)

theorem hasDerivAt_nearAxisVertical (n d p q : ℕ) (P Q scale x y : ℝ)
    (positive : 0 < ((Q+1-y)/3^q)*fermatQuotient n (scale*((Q+1-y)/3^q))) :
    HasDerivAt (fun t => nearAxisLog n d p q P Q scale x t)
      (nearAxisVertical n q Q scale y) y := by
  have inner := ((hasDerivAt_const y (Q+1)).sub (hasDerivAt_id y)).div_const ((3 : ℝ)^q)
  have logarithm := (hasDerivAt_logarithmic_residual n scale ((Q+1-y)/3^q) positive).comp y inner
  have final := logarithm.const_sub ((d : ℝ)*Real.log 3+(n : ℝ)*Real.log ((P+x)/3^p))
  have derivativeIdentity : -(fermatLogDerivative n scale ((Q+1-y)/3^q)*
      ((0-1)/(3 : ℝ)^q)) = nearAxisVertical n q Q scale y := by
    unfold nearAxisVertical
    ring
  apply (final.congr_deriv derivativeIdentity).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t => by rfl)

theorem nearAxisLog_zero (n d p q : ℕ) (P Q x y : ℝ)
    (positive : 0 < n) (valuePositive : 0 < Q+1-y) :
    nearAxisLog n d p q P Q 0 x y =
      (d : ℝ)*Real.log 3+(n : ℝ)*Real.log ((P+x)/3^p)-
        Real.log n-Real.log ((Q+1-y)/3^q) := by
  unfold nearAxisLog
  simp only [zero_mul,fermatQuotient_zero]
  rw [Real.log_mul (show (Q+1-y)/(3 : ℝ)^q ≠ 0 by positivity)
    (show (n : ℝ) ≠ 0 by positivity)]
  ring

theorem nearAxisHorizontal_bounds (n : ℕ) (P x : ℝ) (positiveP : 0 < P)
    (membership : x ∈ Set.Icc (0 : ℝ) 1) :
    (n : ℝ)/(P+1) ≤ nearAxisHorizontal n P x ∧
      nearAxisHorizontal n P x ≤ (n : ℝ)/P := by
  unfold nearAxisHorizontal
  constructor
  · exact div_le_div_of_nonneg_left (by positivity) (by linarith [membership.1])
      (by linarith [membership.2])
  · exact div_le_div_of_nonneg_left (by positivity) positiveP (by linarith [membership.1])

/-- The actual derivative of the normalized exact logarithmic residual converges
uniformly on the entire unit interval, rather than only on the zero curve. -/
theorem nearAxisVertical_uniform (n q : ℕ) (positive : 0 < n)
    (Q error : ℝ) (positiveQ : 0 < Q) (positiveError : 0 < error) :
    ∀ᶠ scale : ℝ in nhds 0, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < ((Q+1-y)/3^q)*fermatQuotient n (scale*((Q+1-y)/3^q)) ∧
      |nearAxisVertical n q Q scale y-1/(Q+1-y)| < error := by
  have powerPositive : (0 : ℝ) < (3 : ℝ)^q := by positivity
  have uniform := near_axis_uniform_C1 n positive (Q/3^q) ((Q+1)/3^q)
    (error*3^q) (by positivity) (by positivity)
  filter_upwards [uniform] with scale uniform
  intro y membership
  have valueMembership : (Q+1-y)/3^q ∈ Set.Icc (Q/(3 : ℝ)^q) ((Q+1)/3^q) := by
    constructor <;> apply (div_le_div_iff_of_pos_right powerPositive).2 <;>
      linarith [membership.1,membership.2]
  have estimate := uniform _ valueMembership
  have valueNonzero : Q+1-y ≠ 0 := by linarith [membership.2]
  refine ⟨estimate.1,?_⟩
  have identity : nearAxisVertical n q Q scale y-1/(Q+1-y) =
      (fermatLogDerivative n scale ((Q+1-y)/3^q)-1/((Q+1-y)/3^q))/3^q := by
    unfold nearAxisVertical
    field_simp [valueNonzero]
    <;> ring
  rw [identity,abs_div,abs_of_pos powerPositive]
  exact (div_lt_iff₀ powerPositive).2 estimate.2.2

theorem continuousAt_nearAxisLog_scale (n d p q : ℕ) (P Q x y : ℝ)
    (positive : 0 < n) (valuePositive : 0 < Q+1-y) :
    ContinuousAt (fun scale : ℝ => nearAxisLog n d p q P Q scale x y) 0 := by
  have valuePositive' : 0 < (Q+1-y)/(3 : ℝ)^q := by positivity
  have residual : Continuous (fun scale : ℝ =>
      ((Q+1-y)/3^q)*fermatQuotient n (scale*((Q+1-y)/3^q))) :=
    continuous_const.mul ((continuous_fermatQuotient n).comp
      (continuous_id.mul continuous_const))
  apply continuousAt_const.sub
  apply residual.continuousAt.log
  simp only [zero_mul,fermatQuotient_zero]
  positivity

theorem continuousOn_nearAxisLog (n d p q : ℕ) (P Q scale : ℝ) (positiveP : 0 < P)
    (positiveResidual : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < ((Q+1-y)/3^q)*fermatQuotient n (scale*((Q+1-y)/3^q))) :
    ContinuousOn (fun point : ℝ × ℝ => nearAxisLog n d p q P Q scale point.1 point.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  have horizontal : Continuous (fun point : ℝ × ℝ => (P+point.1)/(3 : ℝ)^p) :=
    (continuous_const.add continuous_fst).div_const _
  have residual : Continuous (fun point : ℝ × ℝ =>
      ((Q+1-point.2)/3^q)*fermatQuotient n (scale*((Q+1-point.2)/3^q))) :=
    (continuous_rescaled_fermat n).comp
      (continuous_const.prodMk ((continuous_const.sub continuous_snd).div_const _))
  apply (continuousOn_const.add (continuousOn_const.mul
    (horizontal.continuousOn.log ?_))).sub (residual.continuousOn.log ?_)
  · intro point membership
    have positive : 0 < P+point.1 := by linarith [membership.1.1]
    positivity
  · intro point membership
    exact ne_of_gt (positiveResidual point.2 membership.2)

theorem nearAxisLog_corners_persist (n d p q : ℕ) (P Q : ℝ)
    (positive : 0 < n) (positiveQ : 0 < Q)
    (lower : nearAxisLog n d p q P Q 0 0 0 < 0)
    (upper : 0 < nearAxisLog n d p q P Q 0 1 1) :
    ∀ᶠ scale : ℝ in nhds 0,
      nearAxisLog n d p q P Q scale 0 0 < 0 ∧
      0 < nearAxisLog n d p q P Q scale 1 1 := by
  have lowerContinuous := continuousAt_nearAxisLog_scale n d p q P Q 0 0 positive (by linarith)
  have upperContinuous := continuousAt_nearAxisLog_scale n d p q P Q 1 1 positive (by linarith)
  exact (lowerContinuous.eventually (Iio_mem_nhds lower)).and
    (upperContinuous.eventually (Ioi_mem_nhds upper))

end LambdaCantor.Integer
