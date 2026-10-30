import LambdaCantor.Last.EndpointTransferAccepted
import Mathlib.Tactic.FunProp

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

theorem endpoint_scalarWordMap_parameter_continuous (word : List Bool) (coordinate : ℝ) :
    Continuous (fun ratio : ℝ => scalarWordMap ratio word coordinate) := by
  induction word with
  | nil => exact continuous_const
  | cons digit rest induction =>
    cases digit
    · refine (continuous_id.mul induction).congr ?_
      intro ratio
      simp only [Pi.mul_apply, id_eq, scalarWordMap, Bool.false_eq_true, if_false, zero_add]
    · refine (((continuous_const (y := (1 : ℝ))).sub continuous_id).add
        (continuous_id.mul induction)).congr ?_
      intro ratio
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq, scalarWordMap, if_true]

private theorem endpoint_eventually_lt_of_continuousAt
    {first second : ℝ → ℝ} {ratio : ℝ}
    (hfirst : ContinuousAt first ratio) (hsecond : ContinuousAt second ratio)
    (hstrict : first ratio < second ratio) :
    ∀ᶠ parameter in 𝓝 ratio, first parameter < second parameter := by
  have hpositive := (hsecond.sub hfirst).eventually (lt_mem_nhds (sub_pos.mpr hstrict))
  filter_upwards [hpositive] with parameter hparameter
  change 0 < second parameter - first parameter at hparameter
  linarith

private theorem endpoint_two_band_interval_eventually
    {lower upper : ℝ → ℝ} {ratio : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hlower : ContinuousAt lower ratio) (hupper : ContinuousAt upper ratio)
    (horder : lower ratio < upper ratio)
    (bands : TwoBandInterval ratio (lower ratio) (upper ratio)) :
    ∀ᶠ parameter in 𝓝 ratio, TwoBandInterval parameter (lower parameter) (upper parameter) := by
  have hdenominatorFirst : 0 < 1 - ratio := by linarith
  have hdenominatorSecond : 0 < 1 - ratio - ratio ^ 2 := by nlinarith
  have hfirstLower : ContinuousAt (fun parameter : ℝ => 1 / parameter - 1 - parameter) ratio :=
    ((continuousAt_const.div continuousAt_id hpositive.ne').sub continuousAt_const).sub continuousAt_id
  have hsecondLower : ContinuousAt (fun parameter : ℝ => 1 / parameter - 1) ratio :=
    (continuousAt_const.div continuousAt_id hpositive.ne').sub continuousAt_const
  have hfirstUpper : ContinuousAt (fun parameter : ℝ => 1 / (1 - parameter)) ratio :=
    continuousAt_const.div (continuousAt_const.sub continuousAt_id) hdenominatorFirst.ne'
  have hsecondUpper : ContinuousAt (fun parameter : ℝ => 1 / (1 - parameter - parameter ^ 2)) ratio :=
    continuousAt_const.div ((continuousAt_const.sub continuousAt_id).sub (continuousAt_id.pow 2))
      hdenominatorSecond.ne'
  have hone := endpoint_eventually_lt_of_continuousAt continuousAt_const hlower bands.1
  have hordered := endpoint_eventually_lt_of_continuousAt hlower hupper horder
  rcases bands.2.2 with first | second
  · have hleft := endpoint_eventually_lt_of_continuousAt hfirstLower hlower first.1
    have hright := endpoint_eventually_lt_of_continuousAt hupper hfirstUpper first.2
    filter_upwards [hone, hordered, hleft, hright] with parameter hone horder hleft hright
    exact ⟨hone, horder.le, Or.inl ⟨hleft, hright⟩⟩
  · have hleft := endpoint_eventually_lt_of_continuousAt hsecondLower hlower second.1
    have hright := endpoint_eventually_lt_of_continuousAt hupper hsecondUpper second.2
    filter_upwards [hone, hordered, hleft, hright] with parameter hone horder hleft hright
    exact ⟨hone, horder.le, Or.inr ⟨hleft, hright⟩⟩

/-- An accepted endpoint source persists with exactly the same words and
integer offsets. All corner and derivative inequalities are transported by
continuity; no stability of a perfect set is assumed. -/
theorem endpoint_accepted_source_persists {exponent ratio : ℝ}
    (hexponent : 1 < exponent) (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (source : EndpointRectangle exponent ratio) (haccepted : source.Accepted) :
    ∀ᶠ parameter in 𝓝 ratio, 0 < parameter ∧ parameter < 1 / 2 ∧
      ∃ nextSource : EndpointRectangle exponent parameter,
        nextSource.firstWord = source.firstWord ∧ nextSource.secondWord = source.secondWord ∧
        nextSource.firstOffset = source.firstOffset ∧ nextSource.secondOffset = source.secondOffset ∧
        nextSource.Accepted := by
  let firstLeft : ℝ → ℝ := fun parameter => scalarWordMap parameter source.firstWord 0
  let firstRight : ℝ → ℝ := fun parameter => scalarWordMap parameter source.firstWord 1
  let secondLeft : ℝ → ℝ := fun parameter => scalarWordMap parameter source.secondWord 0
  let secondRight : ℝ → ℝ := fun parameter => scalarWordMap parameter source.secondWord 1
  let phase : ℝ := (source.secondOffset : ℝ) - source.firstOffset * exponent
  let coefficient : ℝ → ℝ := fun parameter => exponent * parameter ^ phase
  let powerFactor : ℝ → ℝ := fun parameter =>
    parameter ^ (phase + source.secondWord.length - source.firstWord.length)
  let powerLower : ℝ → ℝ := fun parameter => powerFactor parameter * firstRight parameter ^ (1 - exponent)
  let powerUpper : ℝ → ℝ := fun parameter => powerFactor parameter * firstLeft parameter ^ (1 - exponent)
  let logFactor : ℝ → ℝ := fun parameter =>
    exponent * parameter ^ ((source.firstWord.length : ℝ) - source.secondWord.length)
  let logLower : ℝ → ℝ := fun parameter => logFactor parameter * secondLeft parameter / firstRight parameter
  let logUpper : ℝ → ℝ := fun parameter => logFactor parameter * secondRight parameter / firstLeft parameter
  have hfirstLeft : ContinuousAt firstLeft ratio :=
    (endpoint_scalarWordMap_parameter_continuous source.firstWord 0).continuousAt
  have hfirstRight : ContinuousAt firstRight ratio :=
    (endpoint_scalarWordMap_parameter_continuous source.firstWord 1).continuousAt
  have hsecondLeft : ContinuousAt secondLeft ratio :=
    (endpoint_scalarWordMap_parameter_continuous source.secondWord 0).continuousAt
  have hsecondRight : ContinuousAt secondRight ratio :=
    (endpoint_scalarWordMap_parameter_continuous source.secondWord 1).continuousAt
  have hfirstWidth : firstLeft ratio < firstRight ratio := by
    dsimp only [firstLeft, firstRight]
    rw [scalarWordMap_affine ratio source.firstWord 1]
    nlinarith [pow_pos hpositive source.firstWord.length]
  have hsecondWidth : secondLeft ratio < secondRight ratio := by
    dsimp only [secondLeft, secondRight]
    rw [scalarWordMap_affine ratio source.secondWord 1]
    nlinarith [pow_pos hpositive source.secondWord.length]
  have hfirstPositive : 0 < firstLeft ratio := source.first_positive
  have hsecondPositive : 0 < secondLeft ratio := source.second_positive
  have hfirstRightPositive : 0 < firstRight ratio := hfirstPositive.trans hfirstWidth
  have hsecondRightPositive : 0 < secondRight ratio := hsecondPositive.trans hsecondWidth
  have hexponentPositive : 0 < exponent := by linarith
  have hcoefficient : ContinuousAt coefficient ratio :=
    continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl hpositive.ne'))
  have hpowerFactor : ContinuousAt powerFactor ratio :=
    continuousAt_id.rpow_const (Or.inl hpositive.ne')
  have hlogFactor : ContinuousAt logFactor ratio :=
    continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl hpositive.ne'))
  have hpowerLower : ContinuousAt powerLower ratio :=
    hpowerFactor.mul (hfirstRight.rpow_const (Or.inl hfirstRightPositive.ne'))
  have hpowerUpper : ContinuousAt powerUpper ratio :=
    hpowerFactor.mul (hfirstLeft.rpow_const (Or.inl hfirstPositive.ne'))
  have hlogLower : ContinuousAt logLower ratio :=
    (hlogFactor.mul hsecondLeft).div hfirstRight hfirstRightPositive.ne'
  have hlogUpper : ContinuousAt logUpper ratio :=
    (hlogFactor.mul hsecondRight).div hfirstLeft hfirstPositive.ne'
  have hpowerFactorPositive : 0 < powerFactor ratio := Real.rpow_pos_of_pos hpositive _
  have hlogFactorPositive : 0 < logFactor ratio :=
    mul_pos hexponentPositive (Real.rpow_pos_of_pos hpositive _)
  have hpowerLowerPositive : 0 < powerLower ratio :=
    mul_pos hpowerFactorPositive (Real.rpow_pos_of_pos hfirstRightPositive _)
  have hpowerOrder : powerLower ratio < powerUpper ratio :=
    mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg hfirstPositive hfirstWidth (by linarith))
      hpowerFactorPositive
  have hpowerUpperPositive : 0 < powerUpper ratio := hpowerLowerPositive.trans hpowerOrder
  have hlogLowerPositive : 0 < logLower ratio :=
    div_pos (mul_pos hlogFactorPositive hsecondPositive) hfirstRightPositive
  have hlogOrder : logLower ratio < logUpper ratio := by
    exact (div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hsecondWidth hlogFactorPositive)
      hfirstRightPositive).trans_le
      (div_le_div₀ (mul_pos hlogFactorPositive hsecondRightPositive).le (le_refl _)
        hfirstPositive hfirstWidth.le)
  have hlogUpperPositive : 0 < logUpper ratio := hlogLowerPositive.trans hlogOrder
  have hbands : ∀ᶠ parameter in 𝓝 ratio,
      TwoBandInterval parameter (powerLower parameter) (powerUpper parameter) ∨
      TwoBandInterval parameter (1 / powerUpper parameter) (1 / powerLower parameter) ∨
      TwoBandInterval parameter (logLower parameter) (logUpper parameter) ∨
      TwoBandInterval parameter (1 / logUpper parameter) (1 / logLower parameter) := by
    rcases haccepted with hpower | hpowerReciprocal | hlog | hlogReciprocal
    · exact (endpoint_two_band_interval_eventually hpositive hhalf hpowerLower hpowerUpper hpowerOrder hpower).mono
        (fun _ hband => Or.inl hband)
    · exact (endpoint_two_band_interval_eventually hpositive hhalf
        (continuousAt_const.div hpowerUpper hpowerUpperPositive.ne')
        (continuousAt_const.div hpowerLower hpowerLowerPositive.ne')
        (one_div_lt_one_div_of_lt hpowerLowerPositive hpowerOrder) hpowerReciprocal).mono
        (fun _ hband => Or.inr (Or.inl hband))
    · exact (endpoint_two_band_interval_eventually hpositive hhalf hlogLower hlogUpper hlogOrder hlog).mono
        (fun _ hband => Or.inr (Or.inr (Or.inl hband)))
    · exact (endpoint_two_band_interval_eventually hpositive hhalf
        (continuousAt_const.div hlogUpper hlogUpperPositive.ne')
        (continuousAt_const.div hlogLower hlogLowerPositive.ne')
        (one_div_lt_one_div_of_lt hlogLowerPositive hlogOrder) hlogReciprocal).mono
        (fun _ hband => Or.inr (Or.inr (Or.inr hband)))
  have hfirstEventual := endpoint_eventually_lt_of_continuousAt continuousAt_const hfirstLeft hfirstPositive
  have hsecondEventual := endpoint_eventually_lt_of_continuousAt continuousAt_const hsecondLeft hsecondPositive
  have hlowerCorner := endpoint_eventually_lt_of_continuousAt
    (hfirstLeft.rpow_const (Or.inl hfirstPositive.ne')) (hcoefficient.mul hsecondRight) source.lower_corner
  have hupperCorner := endpoint_eventually_lt_of_continuousAt
    (hcoefficient.mul hsecondLeft) (hfirstRight.rpow_const (Or.inl hfirstRightPositive.ne')) source.upper_corner
  have hparameterPositive : ∀ᶠ parameter : ℝ in 𝓝 ratio, 0 < parameter :=
    eventually_gt_nhds hpositive
  have hparameterHalf : ∀ᶠ parameter : ℝ in 𝓝 ratio, parameter < 1 / 2 :=
    eventually_lt_nhds hhalf
  filter_upwards [hparameterPositive, hparameterHalf, hfirstEventual, hsecondEventual,
    hlowerCorner, hupperCorner, hbands] with parameter hpositive hhalf hfirst hsecond hlower hupper hband
  let nextSource : EndpointRectangle exponent parameter := {
    firstWord := source.firstWord
    secondWord := source.secondWord
    firstOffset := source.firstOffset
    secondOffset := source.secondOffset
    first_positive := hfirst
    second_positive := hsecond
    lower_corner := hlower
    upper_corner := hupper }
  exact ⟨hpositive, hhalf, nextSource, rfl, rfl, rfl, rfl, hband⟩

/-- The actual positive-dimensional endpoint source persists when the Cantor
contraction varies. The same finite endpoint data are retained internally. -/
theorem endpoint_source_positive_dimension_neighborhood {exponent ratio : ℝ}
    (hexponent : 1 < exponent) (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (source : EndpointRectangle exponent ratio) (haccepted : source.Accepted) :
    ∀ᶠ parameter in 𝓝 ratio, 0 < dimH (intersection exponent parameter) := by
  filter_upwards [endpoint_accepted_source_persists hexponent hpositive hhalf source haccepted]
    with parameter hparameter
  obtain ⟨nextSource, _, _, _, _, hacceptedNext⟩ := hparameter.2.2
  exact endpoint_source_positive_dimension hexponent hparameter.1 hparameter.2.1 nextSource hacceptedNext

end LambdaCantor.Last

#print axioms LambdaCantor.Last.endpoint_accepted_source_persists
#print axioms LambdaCantor.Last.endpoint_source_positive_dimension_neighborhood
