import LambdaCantor.AE.CenteredTransversality
import LambdaCantor.AE.CenteredCenterBound
import LambdaCantor.AE.CenteredRootWindow
import LambdaCantor.AE.CenteredWindowPower

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.AE

theorem centered_depths_have_unique_roots {exponent center lower upper : ℝ}
    (hexponent : 1 < exponent) (hlower : 0 < lower)
    (hcenterLower : lower < center) (hcenterUpper : center < upper) (hless : upper < 1)
    (horizontalDepth verticalDepth : ℕ → ℕ)
    (hdepth : ∀ index, index ≤ verticalDepth index) (htwo : ∀ index, 2 ≤ verticalDepth index)
    (hphase : ∀ index, |(verticalDepth index : ℝ) - exponent * horizontalDepth index +
      Real.log exponent / Real.log center| ≤ (center ^ index) ^ 2)
    (hdecay : ∀ index, (verticalDepth index : ℝ) ^ 2 * upper ^ verticalDepth index ≤ (center ^ index) ^ 3)
    (hremainder : ∀ ratios : ℕ → ℝ, (∀ index, ratios index ∈ Set.Icc lower upper) →
      ∀ digits : ℕ → ℕ → Bool,
        Tendsto (fun index => centeredRemainderFirst exponent (horizontalDepth index)
          (verticalDepth index) index (digits index) (ratios index)) atTop (𝓝 0)) :
    ∃ width : ℝ, 0 < width ∧ ∀ᶠ index : ℕ in atTop, ∀ digits : ℕ → Bool × Bool,
      ∃! root : ℝ, root ∈ Set.Icc (center - width * center ^ index) (center + width * center ^ index) ∧
        centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index digits root = 0 := by
  have hcenter := hlower.trans hcenterLower
  have hcenterLess := hcenterUpper.trans hless
  have hdiscrepancy := centered_resonance_exponent_positive hexponent hcenter hcenterLess
  have hexponentPositive : 0 < exponent := by linarith
  let slope := exponent * (-Real.log exponent / Real.log center) *
    center ^ (-Real.log exponent / Real.log center - 1) / 2
  have hslope : 0 < slope := by dsimp [slope]; positivity
  obtain ⟨errorBound, herrorBound, hcenterBound⟩ := centered_center_residual_eventual_bound
    hexponent hcenter hcenterUpper.le hless horizontalDepth verticalDepth hdepth htwo hphase hdecay
  let width := (errorBound + 1) / slope
  have hwidth : 0 < width := by dsimp [width]; positivity
  have hwidthSlope : errorBound < slope * width := by
    have hidentity : slope * width = errorBound + 1 := by
      dsimp [width]
      field_simp [hslope.ne']
    rw [hidentity]
    linarith
  refine ⟨width, hwidth, ?_⟩
  have hnegative := centered_uniform_negative_derivative hexponent hcenter hcenterLess hlower
    ⟨hcenterLower.le, hcenterUpper.le⟩ hless hwidth.le horizontalDepth verticalDepth hdepth hphase hremainder
  have hwindow := centered_window_eventually_mem_nhds (windowConstant := width)
    hcenter hcenterLess (Ioo_mem_nhds hcenterLower hcenterUpper)
  have hpowerSmall : ∀ᶠ index : ℕ in atTop, upper ^ index < (1 / 2 : ℝ) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (hcenter.le.trans hcenterUpper.le) hless).eventually
      (gt_mem_nhds (by norm_num))
  filter_upwards [hnegative, hwindow, hpowerSmall, hcenterBound]
    with index hnegative hwindow hpowerSmall hcenterBound
  intro digits
  have hwindowDistance : ∀ parameter ∈ Set.Icc (center - width * center ^ index) (center + width * center ^ index),
      |parameter - center| ≤ width * center ^ index := by
    intro parameter hparameter
    apply abs_le.mpr
    constructor <;> linarith [hparameter.1, hparameter.2]
  have hband : ∀ parameter ∈ Set.Icc (center - width * center ^ index) (center + width * center ^ index),
      parameter ∈ Set.Ioo lower upper := fun parameter hparameter =>
    hwindow parameter (hwindowDistance parameter hparameter)
  have hdifferentiable : ∀ parameter ∈ Set.Icc (center - width * center ^ index) (center + width * center ^ index),
      DifferentiableAt ℝ (centeredNormalizedResidual exponent (horizontalDepth index)
        (verticalDepth index) index digits) parameter := by
    intro parameter hparameter
    have hparameterBand := hband parameter hparameter
    have hpositive := hlower.trans hparameterBand.1
    have hparameterLess := hparameterBand.2.trans hless
    have htailPower : parameter ^ index < 1 / 2 :=
      (pow_le_pow_left₀ hpositive.le hparameterBand.2.le _).trans_lt hpowerSmall
    have hhorizontal := centeredHorizontalFactor_bounds index (fun position => (digits position).1) hpositive hparameterLess
    have hhorizontalPositive : 0 < centeredHorizontalFactor index (fun position => (digits position).1) parameter := by
      have := (abs_le.mp hhorizontal).1
      linarith
    have hverticalPower : parameter ^ verticalDepth index < 1 :=
      ((pow_le_pow_left₀ hpositive.le hparameterBand.2.le _).trans
        (pow_le_pow_of_le_one (hcenter.le.trans hcenterUpper.le)
          hless.le (hdepth index))).trans_lt (by linarith : upper ^ index < 1)
    exact (centeredNormalizedResidual_hasDerivAt exponent (horizontalDepth index) (verticalDepth index)
      index digits hpositive hparameterLess hhorizontalPositive hverticalPower).differentiableAt
  apply centered_root_window_exists_unique (pow_pos hcenter _) hwidth hslope hwidthSlope
    (fun parameter hparameter => (hdifferentiable parameter hparameter).continuousAt.continuousWithinAt)
    (fun parameter hparameter => (hdifferentiable parameter ⟨hparameter.1.le, hparameter.2.le⟩).differentiableWithinAt)
  · intro parameter hparameter
    have hclosed : parameter ∈ Set.Icc (center - width * center ^ index) (center + width * center ^ index) :=
      ⟨hparameter.1.le, hparameter.2.le⟩
    have hvalue := hnegative digits parameter
      ⟨(hband parameter hclosed).1.le, (hband parameter hclosed).2.le⟩ (hwindowDistance parameter hclosed)
    dsimp [slope]
    linarith
  · exact hcenterBound digits

/-- Actual centered roots for every irrational exponent greater than one.
No root-family or analytic-remainder hypothesis is assumed. -/
theorem irrational_centered_roots {exponent center lower upper : ℝ}
    (hirrational : Irrational exponent) (hexponent : 1 < exponent) (hlower : 0 < lower)
    (hcenterLower : lower < center) (hcenterUpper : center < upper) (hless : upper < 1) :
    ∃ horizontalDepth verticalDepth : ℕ → ℕ, ∃ width : ℝ, 0 < width ∧
      (∀ index, index ≤ horizontalDepth index ∧ index ≤ verticalDepth index ∧ 2 ≤ verticalDepth index) ∧
      (∀ index, |(verticalDepth index : ℝ) - exponent * horizontalDepth index +
        Real.log exponent / Real.log center| < (center ^ index) ^ 2 ∧
        (verticalDepth index : ℝ) ^ 2 * upper ^ verticalDepth index < (center ^ index) ^ 3) ∧
      ∀ᶠ index : ℕ in atTop, ∀ digits : ℕ → Bool × Bool,
        ∃! root : ℝ, root ∈ Set.Icc (center - width * center ^ index) (center + width * center ^ index) ∧
          centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index digits root = 0 := by
  have hcenter := hlower.trans hcenterLower
  have hcenterLess := hcenterUpper.trans hless
  obtain ⟨horizontalDepth, verticalDepth, hdepth, hchoice, hC2⟩ := centered_actual_C2_depth_sequences
    hirrational hexponent hcenter hcenterLess hlower (hcenterLower.le.trans hcenterUpper.le) hless
  obtain ⟨width, hwidth, hroots⟩ := centered_depths_have_unique_roots hexponent hlower hcenterLower
    hcenterUpper hless horizontalDepth verticalDepth (fun index => (hdepth index).2.1)
    (fun index => (hdepth index).2.2) (fun index => (hchoice index).1.le)
    (fun index => (hchoice index).2.le)
    (fun ratios hratios digits => (hC2 ratios hratios digits).2.1)
  exact ⟨horizontalDepth, verticalDepth, width, hwidth, hdepth, hchoice, hroots⟩

end LambdaCantor.AE
