import LambdaCantor.Last.TwoBandCriterion

noncomputable section
namespace LambdaCantor.Last

theorem two_band_swapped_strict_derivative {function : (ℝ × ℝ) → ℝ}
    {derivativeS derivativeT : ℝ} (point : ℝ × ℝ)
    (hderivative : HasStrictFDerivAt function
      (derivativeS • ContinuousLinearMap.fst ℝ ℝ ℝ +
        derivativeT • ContinuousLinearMap.snd ℝ ℝ ℝ) point.swap) :
    HasStrictFDerivAt (fun value : ℝ × ℝ => function value.swap)
      (derivativeT • ContinuousLinearMap.fst ℝ ℝ ℝ +
        derivativeS • ContinuousLinearMap.snd ℝ ℝ ℝ) point := by
  have hswap := (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := point)).prodMk
    (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := point))
  apply (hderivative.comp point hswap).congr_fderiv
  apply ContinuousLinearMap.ext
  intro value
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

/-- The coordinate-exchanged form of the full two-band criterion. -/
theorem two_band_positive_derivative_criterion_reciprocal
    (function : (ℝ × ℝ) → ℝ) (derivativeS derivativeT : (ℝ × ℝ) → ℝ)
    {lowerS upperS lowerT upperT ratio level : ℝ}
    (hcontinuous : Continuous function) (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hlowerS : 0 < lowerS) (horderS : lowerS ≤ upperS)
    (hlowerT : 0 < lowerT) (horderT : lowerT ≤ upperT)
    (bands : TwoBandInterval ratio (lowerS / upperT) (upperS / lowerT))
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
  have hswapped : 0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧ function point.swap = level} := by
    apply two_band_positive_derivative_criterion
      (fun point : ℝ × ℝ => function point.swap)
      (fun point => derivativeT point.swap) (fun point => derivativeS point.swap)
      (hcontinuous.comp (continuous_snd.prodMk continuous_fst))
      hpositive hhalf hlowerT horderT bands
    · intro point hwidth hheight
      exact two_band_swapped_strict_derivative point (hstrict point.swap hheight hwidth)
    · intro point hwidth hheight
      exact hboundT point.swap hheight hwidth
    · intro point hwidth hheight
      exact hboundS point.swap hheight hwidth
    · exact hlevel
  have hswap : Isometry (Prod.swap : ℝ × ℝ → ℝ × ℝ) := by
    apply Isometry.of_dist_eq
    intro first second
    simp only [Prod.dist_eq, Prod.fst_swap, Prod.snd_swap, max_comm]
  apply hswapped.trans_le ((hswap.antilipschitz.le_dimH_image _).trans (dimH_mono ?_))
  rintro point ⟨value, hvalue, rfl⟩
  exact ⟨⟨hvalue.1.2, hvalue.1.1⟩, hvalue.2⟩

end LambdaCantor.Last
