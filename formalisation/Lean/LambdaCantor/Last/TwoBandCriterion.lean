import LambdaCantor.Last.TwoBandActual
import LambdaCantor.Last.DerivativeGrowth
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
namespace LambdaCantor.Last

theorem two_band_partial_derivatives_of_strict_derivative
    {function : (ℝ × ℝ) → ℝ} {width height derivativeS derivativeT : ℝ}
    (hderivative : HasStrictFDerivAt function
      (derivativeS • ContinuousLinearMap.fst ℝ ℝ ℝ +
        derivativeT • ContinuousLinearMap.snd ℝ ℝ ℝ) (width, height)) :
    HasDerivAt (fun coordinate => function (coordinate, height)) derivativeS width ∧
      HasDerivAt (fun coordinate => function (width, coordinate)) derivativeT height := by
  constructor
  · convert! hderivative.hasFDerivAt.comp_hasDerivAt width
      ((hasDerivAt_id width).prodMk (hasDerivAt_const width height)) using 1 <;>
      first | rfl | simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  · convert! hderivative.hasFDerivAt.comp_hasDerivAt height
      ((hasDerivAt_const height width).prodMk (hasDerivAt_id height)) using 1 <;>
      first | rfl | simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]

/-- Lemma 4.1 with explicit global derivative bounds. The two ratios are the
extreme cross-variable bounds, so the entire closed interval is in one band. -/
theorem two_band_positive_derivative_criterion
    (function : (ℝ × ℝ) → ℝ) (derivativeS derivativeT : (ℝ × ℝ) → ℝ)
    {lowerS upperS lowerT upperT ratio level : ℝ}
    (hcontinuous : Continuous function) (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hlowerS : 0 < lowerS) (horderS : lowerS ≤ upperS)
    (bands : TwoBandInterval ratio (lowerT / upperS) (upperT / lowerS))
    (hstrict : ∀ point : ℝ × ℝ, point.1 ∈ Set.Icc (0 : ℝ) 1 →
      point.2 ∈ Set.Icc (0 : ℝ) 1 → HasStrictFDerivAt function
        (derivativeS point • ContinuousLinearMap.fst ℝ ℝ ℝ +
          derivativeT point • ContinuousLinearMap.snd ℝ ℝ ℝ) point)
    (hboundS : ∀ point : ℝ × ℝ, point.1 ∈ Set.Icc (0 : ℝ) 1 →
      point.2 ∈ Set.Icc (0 : ℝ) 1 → lowerS ≤ derivativeS point ∧ derivativeS point ≤ upperS)
    (hboundT : ∀ point : ℝ × ℝ, point.1 ∈ Set.Icc (0 : ℝ) 1 →
      point.2 ∈ Set.Icc (0 : ℝ) 1 → lowerT ≤ derivativeT point ∧ derivativeT point ≤ upperT)
    (hlevel : level ∈ Set.Ioo (function (0, 0)) (function (1, 1))) :
    0 < dimH {point | point ∈ cantorDust ratio ∧ function point = level} := by
  have hupperS : 0 < upperS := hlowerS.trans_le horderS
  have hslope : upperS < lowerT := by
    have hbound := (lt_div_iff₀ hupperS).mp bands.1
    simpa using hbound
  have hlowerT : 0 < lowerT := hupperS.trans hslope
  have hlow := TwoBandSlopes.common_inequalities hpositive hhalf
    (bands.slope (le_refl _) bands.2.1)
  have hupp := TwoBandSlopes.common_inequalities hpositive hhalf
    (bands.slope bands.2.1 (le_refl _))
  have hshell : (1 - ratio - ratio ^ 2) * upperS < ratio * lowerT := by
    have hbound := mul_lt_mul_of_pos_right hlow.1 hupperS
    field_simp [hupperS.ne'] at hbound
    nlinarith
  have houter : (1 - 2 * ratio) * upperS < ratio * lowerT := by
    have hbound := mul_lt_mul_of_pos_right hlow.2.2.2 hupperS
    field_simp [hupperS.ne'] at hbound
    nlinarith
  have hmiddle : (1 - 2 * ratio) * upperT < lowerS := by
    have hbound := mul_lt_mul_of_pos_right hupp.2.2.1 hlowerS
    field_simp [hlowerS.ne'] at hbound
    nlinarith
  have growth := coordinateGrowth_of_partial_derivatives
    (fun width hwidth height hheight =>
      (two_band_partial_derivatives_of_strict_derivative (hstrict (width, height) hwidth hheight)).1)
    (fun width hwidth height hheight =>
      (two_band_partial_derivatives_of_strict_derivative (hstrict (width, height) hwidth hheight)).2)
    (fun width hwidth height hheight => hboundS (width, height) hwidth hheight)
    (fun width hwidth height hheight => hboundT (width, height) hwidth hheight)
  apply positive_dimension_of_two_band_coordinate_growth growth hcontinuous hpositive hhalf
    hlowerS hslope hshell houter hmiddle _ hlevel
  intro point hpoint
  have hwidth := cantorSet_subset_unitInterval hpositive.le (show ratio < 1 by linarith) hpoint.1
  have hheight := cantorSet_subset_unitInterval hpositive.le (show ratio < 1 by linarith) hpoint.2
  have hS := hboundS point hwidth hheight
  have hT := hboundT point hwidth hheight
  have hSpositive : 0 < derivativeS point := hlowerS.trans_le hS.1
  have hTpositive : 0 < derivativeT point := hlowerT.trans_le hT.1
  have hupperT : 0 < upperT := hTpositive.trans_le hT.2
  have hlower_ratio : lowerT / upperS ≤ derivativeT point / derivativeS point := by
    rw [div_le_div_iff₀ hupperS hSpositive]
    nlinarith [mul_nonneg (sub_nonneg.mpr hS.2) hlowerT.le,
      mul_nonneg (sub_nonneg.mpr hT.1) hupperS.le]
  have hupper_ratio : derivativeT point / derivativeS point ≤ upperT / lowerS := by
    rw [div_le_div_iff₀ hSpositive hlowerS]
    nlinarith [mul_nonneg (sub_nonneg.mpr hS.1) hupperT.le,
      mul_nonneg (sub_nonneg.mpr hT.2) hlowerS.le]
  refine ⟨derivativeS point, derivativeT point / derivativeS point, hSpositive,
    bands.slope hlower_ratio hupper_ratio, ?_⟩
  have hproduct := (hstrict point hwidth hheight).const_mul (derivativeS point)⁻¹
  have hlinear : (derivativeS point)⁻¹ •
      (derivativeS point • ContinuousLinearMap.fst ℝ ℝ ℝ +
        derivativeT point • ContinuousLinearMap.snd ℝ ℝ ℝ) =
      positiveLinearContinuous (derivativeT point / derivativeS point) := by
    apply ContinuousLinearMap.ext
    intro increment
    change (derivativeS point)⁻¹ *
      (derivativeS point * increment.1 + derivativeT point * increment.2) =
        increment.1 + (derivativeT point / derivativeS point) * increment.2
    field_simp [hSpositive.ne']
    <;> ring
  rw [hlinear] at hproduct
  have hfunction : (fun value : ℝ × ℝ => (derivativeS point)⁻¹ * function value) =
      fun value => function value / derivativeS point := by
    funext value
    simp only [div_eq_mul_inv, mul_comm]
  rw [hfunction] at hproduct
  exact hproduct

end LambdaCantor.Last
