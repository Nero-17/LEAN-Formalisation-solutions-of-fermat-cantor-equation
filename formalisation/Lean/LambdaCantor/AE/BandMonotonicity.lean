import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Set MeasureTheory

namespace LambdaCantor.AE

/-- A nonnegative continuous weight, positive precisely in the open band. -/
noncomputable def bandWeight (band point : ℝ) : ℝ := max 0 (band ^ 2 - point ^ 2)

/-- A differentiable saturation primitive. Its derivative vanishes outside
the band, while it is strictly increasing inside. -/
noncomputable def bandPrimitive (band point : ℝ) : ℝ := ∫ value in (0 : ℝ)..point, bandWeight band value

theorem continuous_bandWeight (band : ℝ) : Continuous (bandWeight band) := by
  unfold bandWeight
  exact continuous_const.max (continuous_const.sub (continuous_id.pow 2))

theorem hasDerivAt_bandPrimitive (band point : ℝ) :
    HasDerivAt (bandPrimitive band) (bandWeight band point) point := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((continuous_bandWeight band).intervalIntegrable 0 point)
    (continuous_bandWeight band).aestronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_bandWeight band).continuousAt

theorem monotone_bandPrimitive (band : ℝ) : Monotone (bandPrimitive band) := by
  apply monotone_of_deriv_nonneg
  · exact fun point => (hasDerivAt_bandPrimitive band point).differentiableAt
  · intro point
    rw [(hasDerivAt_bandPrimitive band point).deriv]
    exact le_max_left _ _

theorem strictMonoOn_bandPrimitive {band : ℝ} (hband : 0 < band) :
    StrictMonoOn (bandPrimitive band) (Icc (-band) band) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact (continuous_iff_continuousAt.mpr
      (fun point => (hasDerivAt_bandPrimitive band point).continuousAt)).continuousOn
  · intro point hpoint
    rw [interior_Icc] at hpoint
    rw [(hasDerivAt_bandPrimitive band point).deriv]
    have hpositive : 0 < band ^ 2 - point ^ 2 := by
      have hproduct := mul_pos (sub_pos.mpr hpoint.2)
        (show 0 < band + point by linarith [hpoint.1])
      nlinarith
    exact hpositive.trans_le (le_max_right _ _)

theorem bandWeight_eq_zero_of_outside {band point : ℝ}
    (hband : 0 < band) (houtside : ¬ |point| < band) : bandWeight band point = 0 := by
  have hsquare := mul_self_le_mul_self hband.le (le_of_not_gt houtside)
  unfold bandWeight
  apply max_eq_left
  nlinarith [sq_abs point]

/-- Clipping by the differentiable primitive turns a derivative condition
only in a value band into a global antitonicity statement on the domain. -/
theorem antitoneOn_bandPrimitive_comp
    {domain : Set ℝ} (hconvex : Convex ℝ domain)
    {function : ℝ → ℝ} {band : ℝ} (hband : 0 < band)
    (hdifferentiable : ∀ point ∈ domain, DifferentiableAt ℝ function point)
    (hnegative : ∀ point ∈ domain, |function point| < band → deriv function point < 0) :
    AntitoneOn (fun point => bandPrimitive band (function point)) domain := by
  have hderivative : ∀ point ∈ domain,
      HasDerivAt (fun parameter => bandPrimitive band (function parameter))
        (bandWeight band (function point) * deriv function point) point := by
    intro point hpoint
    exact (hasDerivAt_bandPrimitive band (function point)).comp point
      (hdifferentiable point hpoint).hasDerivAt
  apply antitoneOn_of_deriv_nonpos hconvex
  · intro point hpoint
    exact (hderivative point hpoint).continuousAt.continuousWithinAt
  · intro point hpoint
    exact (hderivative point (interior_subset hpoint)).differentiableAt.differentiableWithinAt
  · intro point hpoint
    rw [(hderivative point (interior_subset hpoint)).deriv]
    by_cases hinside : |function point| < band
    · exact mul_nonpos_of_nonneg_of_nonpos (le_max_left _ _)
        (hnegative point (interior_subset hpoint) hinside).le
    · rw [bandWeight_eq_zero_of_outside hband hinside, zero_mul]

/-- The band preimage is convex as a consequence of the clipped
antitonicity. Convexity of this preimage is proved, not assumed. -/
theorem convex_preimage_band_of_antitone_primitive
    {domain : Set ℝ} (hconvex : Convex ℝ domain)
    {function : ℝ → ℝ} {band : ℝ} (hband : 0 < band)
    (hantitone : AntitoneOn (fun point => bandPrimitive band (function point)) domain) :
    Convex ℝ (domain ∩ function ⁻¹' Ioo (-band) band) := by
  apply (convex_iff_ordConnected).mpr
  rw [ordConnected_iff]
  intro left hleft right hright horder point hpoint
  have hdomain : point ∈ domain := hconvex.ordConnected.out hleft.1 hright.1 hpoint
  refine ⟨hdomain, ?_⟩
  have hupper := hantitone hleft.1 hdomain hpoint.1
  have hlower := hantitone hdomain hright.1 hpoint.2
  have hprimitive := strictMonoOn_bandPrimitive hband
  have hleftendpoint : -band ∈ Icc (-band) band := ⟨le_rfl, by linarith⟩
  have hrightendpoint : band ∈ Icc (-band) band := ⟨by linarith, le_rfl⟩
  have hleftvalue : function left ∈ Icc (-band) band := ⟨hleft.2.1.le, hleft.2.2.le⟩
  have hrightvalue : function right ∈ Icc (-band) band := ⟨hright.2.1.le, hright.2.2.le⟩
  constructor
  · by_contra hnot
    have hbelow := monotone_bandPrimitive band (le_of_not_gt hnot)
    have hstrict := hprimitive hleftendpoint hrightvalue hright.2.1
    exact (not_lt_of_ge (hlower.trans hbelow)) hstrict
  · by_contra hnot
    have habove := monotone_bandPrimitive band (le_of_not_gt hnot)
    have hstrict := hprimitive hleftvalue hrightendpoint hleft.2.2
    exact (not_lt_of_ge (habove.trans hupper)) hstrict

/-- Fixed negative derivative in a value band implies strict antitonicity
on the entire band preimage, even before its connectedness is known. This
justifies the single change-of-variables branch in the pair-annulus proof. -/
theorem strictAntiOn_of_deriv_neg_on_band
    {domain : Set ℝ} (hconvex : Convex ℝ domain)
    {function : ℝ → ℝ} {band : ℝ} (hband : 0 < band)
    (hdifferentiable : ∀ point ∈ domain, DifferentiableAt ℝ function point)
    (hnegative : ∀ point ∈ domain, |function point| < band → deriv function point < 0) :
    StrictAntiOn function (domain ∩ function ⁻¹' Ioo (-band) band) := by
  have hantitone := antitoneOn_bandPrimitive_comp hconvex hband hdifferentiable hnegative
  have hbandconvex := convex_preimage_band_of_antitone_primitive hconvex hband hantitone
  apply strictAntiOn_of_deriv_neg hbandconvex
  · intro point hpoint
    exact (hdifferentiable point hpoint.1).continuousAt.continuousWithinAt
  · intro point hpoint
    have hmembership := interior_subset hpoint
    exact hnegative point hmembership.1 (abs_lt.mpr hmembership.2)

end LambdaCantor.AE
