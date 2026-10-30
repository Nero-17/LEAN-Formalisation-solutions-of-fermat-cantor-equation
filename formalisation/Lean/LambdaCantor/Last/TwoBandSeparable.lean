import LambdaCantor.Last.TwoBandCriterion
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Order.Compact

noncomputable section
namespace LambdaCantor.Last

/-- The separable C1 version of Lemma 4.1. The individual derivative bounds
are obtained from compact extrema, rather than supplied as extra hypotheses.
Here C1 functions on the unit interval are represented by ambient C1 functions. -/
theorem two_band_separable_c1_criterion
    {first second : ℝ → ℝ} {ratio level lower upper : ℝ}
    (hfirst : ContDiff ℝ 1 first) (hsecond : ContDiff ℝ 1 second)
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hfirst_positive : ∀ coordinate ∈ Set.Icc (0 : ℝ) 1, 0 < deriv first coordinate)
    (hsecond_positive : ∀ coordinate ∈ Set.Icc (0 : ℝ) 1, 0 < deriv second coordinate)
    (bands : TwoBandInterval ratio lower upper)
    (hratios : ∀ firstCoordinate ∈ Set.Icc (0 : ℝ) 1,
      ∀ secondCoordinate ∈ Set.Icc (0 : ℝ) 1,
        lower ≤ deriv second secondCoordinate / deriv first firstCoordinate ∧
        deriv second secondCoordinate / deriv first firstCoordinate ≤ upper)
    (hlevel : level ∈ Set.Ioo (first 0 + second 0) (first 1 + second 1)) :
    0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧
      first point.1 + second point.2 = level} := by
  have hnonempty : (Set.Icc (0 : ℝ) 1).Nonempty := Set.nonempty_Icc.mpr zero_le_one
  obtain ⟨firstMinimum, hfirstMinimum, hfirstLower⟩ :=
    isCompact_Icc.exists_isMinOn hnonempty hfirst.continuous_deriv_one.continuousOn
  obtain ⟨firstMaximum, hfirstMaximum, hfirstUpper⟩ :=
    isCompact_Icc.exists_isMaxOn hnonempty hfirst.continuous_deriv_one.continuousOn
  obtain ⟨secondMinimum, hsecondMinimum, hsecondLower⟩ :=
    isCompact_Icc.exists_isMinOn hnonempty hsecond.continuous_deriv_one.continuousOn
  obtain ⟨secondMaximum, hsecondMaximum, hsecondUpper⟩ :=
    isCompact_Icc.exists_isMaxOn hnonempty hsecond.continuous_deriv_one.continuousOn
  have hfirst_order := hfirstLower hfirstMaximum
  have hsecond_order := hsecondLower hsecondMaximum
  have hlower_ratio := (hratios firstMaximum hfirstMaximum secondMinimum hsecondMinimum).1
  have hupper_ratio := (hratios firstMinimum hfirstMinimum secondMaximum hsecondMaximum).2
  have hordered : deriv second secondMinimum / deriv first firstMaximum ≤
      deriv second secondMaximum / deriv first firstMinimum :=
    div_le_div₀ (hsecond_positive secondMaximum hsecondMaximum).le hsecond_order
      (hfirst_positive firstMinimum hfirstMinimum) hfirst_order
  have hbands : TwoBandInterval ratio
      (deriv second secondMinimum / deriv first firstMaximum)
      (deriv second secondMaximum / deriv first firstMinimum) := by
    refine ⟨bands.1.trans_le hlower_ratio, hordered, ?_⟩
    rcases bands.2.2 with firstBand | secondBand
    · exact Or.inl ⟨firstBand.1.trans_le hlower_ratio, hupper_ratio.trans_lt firstBand.2⟩
    · exact Or.inr ⟨secondBand.1.trans_le hlower_ratio, hupper_ratio.trans_lt secondBand.2⟩
  apply two_band_positive_derivative_criterion
    (fun point : ℝ × ℝ => first point.1 + second point.2)
    (fun point => deriv first point.1) (fun point => deriv second point.2)
    ((hfirst.continuous.comp continuous_fst).add (hsecond.continuous.comp continuous_snd))
    hpositive hhalf (hfirst_positive firstMinimum hfirstMinimum) hfirst_order hbands
  · intro point hwidth hheight
    have hfirstStrict := (hfirst.hasStrictDerivAt (by norm_num)).comp_hasStrictFDerivAt point
      (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := point))
    have hsecondStrict := (hsecond.hasStrictDerivAt (by norm_num)).comp_hasStrictFDerivAt point
      (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := point))
    exact hfirstStrict.add hsecondStrict
  · intro point hwidth hheight
    exact ⟨hfirstLower hwidth, hfirstUpper hwidth⟩
  · intro point hwidth hheight
    exact ⟨hsecondLower hheight, hsecondUpper hheight⟩
  · exact hlevel

end LambdaCantor.Last
