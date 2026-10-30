import LambdaCantor.Last.TwoBandSeparable
import LambdaCantor.Last.ClosedIntervalC1Extension

noncomputable section
namespace LambdaCantor.Last

/-- Lemma 4.1 for C1 functions on the closed unit interval, using one-sided
derivatives at endpoints. No ambient smoothness or individual derivative bounds
are assumed; the extension and compact extrema are constructed internally. -/
theorem two_band_separable_c1_closed_interval_criterion
    {first second : ℝ → ℝ} {ratio level lower upper : ℝ}
    (hfirst : ContDiffOn ℝ 1 first (Set.Icc (0 : ℝ) 1))
    (hsecond : ContDiffOn ℝ 1 second (Set.Icc (0 : ℝ) 1))
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hfirst_positive : ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
      0 < derivWithin first (Set.Icc (0 : ℝ) 1) coordinate)
    (hsecond_positive : ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
      0 < derivWithin second (Set.Icc (0 : ℝ) 1) coordinate)
    (bands : TwoBandInterval ratio lower upper)
    (hratios : ∀ firstCoordinate ∈ Set.Icc (0 : ℝ) 1,
      ∀ secondCoordinate ∈ Set.Icc (0 : ℝ) 1,
        lower ≤ derivWithin second (Set.Icc (0 : ℝ) 1) secondCoordinate /
          derivWithin first (Set.Icc (0 : ℝ) 1) firstCoordinate ∧
        derivWithin second (Set.Icc (0 : ℝ) 1) secondCoordinate /
          derivWithin first (Set.Icc (0 : ℝ) 1) firstCoordinate ≤ upper)
    (hlevel : level ∈ Set.Ioo (first 0 + second 0) (first 1 + second 1)) :
    0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧
      first point.1 + second point.2 = level} := by
  obtain ⟨firstExtension, hfirstExtension, hfirstEqual, hfirstDerivative⟩ :=
    closed_interval_c1_extension zero_lt_one hfirst
  obtain ⟨secondExtension, hsecondExtension, hsecondEqual, hsecondDerivative⟩ :=
    closed_interval_c1_extension zero_lt_one hsecond
  have hzero : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hone : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hdimension : 0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧
      firstExtension point.1 + secondExtension point.2 = level} := by
    apply two_band_separable_c1_criterion hfirstExtension hsecondExtension hpositive hhalf
    · intro coordinate hcoordinate
      rw [hfirstDerivative hcoordinate]
      exact hfirst_positive coordinate hcoordinate
    · intro coordinate hcoordinate
      rw [hsecondDerivative hcoordinate]
      exact hsecond_positive coordinate hcoordinate
    · exact bands
    · intro firstCoordinate hfirstCoordinate secondCoordinate hsecondCoordinate
      rw [hfirstDerivative hfirstCoordinate, hsecondDerivative hsecondCoordinate]
      exact hratios firstCoordinate hfirstCoordinate secondCoordinate hsecondCoordinate
    · simpa only [hfirstEqual hzero, hfirstEqual hone, hsecondEqual hzero, hsecondEqual hone] using hlevel
  apply hdimension.trans_le (dimH_mono ?_)
  rintro point ⟨hpoint, hlevelPoint⟩
  have hless : ratio < 1 := by linarith
  have hfirstUnit := cantorSet_subset_unitInterval hpositive.le hless hpoint.1
  have hsecondUnit := cantorSet_subset_unitInterval hpositive.le hless hpoint.2
  refine ⟨hpoint, ?_⟩
  simpa only [hfirstEqual hfirstUnit, hsecondEqual hsecondUnit] using hlevelPoint

end LambdaCantor.Last
