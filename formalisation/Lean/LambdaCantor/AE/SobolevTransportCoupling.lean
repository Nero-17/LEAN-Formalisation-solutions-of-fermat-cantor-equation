import LambdaCantor.AE.SobolevTransportTranslation

noncomputable section
open MeasureTheory Filter

namespace LambdaCantor.AE

def mollifiedLaw (law : Measure ℝ) (scale value : ℝ) : ℝ :=
  ∫ location, transportMollifier scale (value - location) ∂law

theorem integrable_transportMollifier_joint {Sample : Type*} [MeasurableSpace Sample]
    (law : Measure Sample) [IsFiniteMeasure law] (coordinate : Sample → ℝ)
    (hcoordinate : Measurable coordinate) {scale : ℝ} (hscale : 0 < scale) :
    Integrable (fun sampleAndValue : Sample × ℝ =>
      transportMollifier scale (sampleAndValue.2 - coordinate sampleAndValue.1))
      (law.prod volume) := by
  apply (integrable_prod_iff
    (((contDiff_transportMollifier scale).continuous.measurable.comp
      (measurable_snd.sub (hcoordinate.comp measurable_fst))).aestronglyMeasurable)).mpr
  constructor
  · exact Eventually.of_forall (fun sample =>
      (integrable_transportMollifier hscale).comp_sub_right (coordinate sample))
  · have hidentity (sample : Sample) :
        (∫ value : ℝ, ‖transportMollifier scale (value - coordinate sample)‖) = 1 := by
      rw [integral_sub_right_eq_self
        (fun value : ℝ => ‖transportMollifier scale value‖) (coordinate sample)]
      simpa only [Real.norm_eq_abs] using integral_abs_transportMollifier hscale
    exact (integrable_const (μ := law) (1 : ℝ)).congr
      (Eventually.of_forall (fun sample => (hidentity sample).symm))

theorem mollifiedLaw_map (law : Measure (ℝ × ℝ)) (coordinate : ℝ × ℝ → ℝ)
    (hcoordinate : Measurable coordinate) (scale value : ℝ) :
    mollifiedLaw (law.map coordinate) scale value =
      ∫ sample, transportMollifier scale (value - coordinate sample) ∂law := by
  unfold mollifiedLaw
  exact integral_map (f := fun location : ℝ => transportMollifier scale (value - location))
    hcoordinate.aemeasurable
    (((contDiff_transportMollifier scale).continuous.comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)

/-- The inverse-scale estimate is applied to the actual common sampling law,
so its right side is precisely the available same-address coupling cost. -/
theorem mollifiedLaw_L1_le_coupling_cost
    {constant : ℝ} (htranslation : ∀ scale : ℝ, 0 < scale → ∀ first second : ℝ,
      (∫ value : ℝ, |transportMollifier scale (value - first) -
        transportMollifier scale (value - second)|) ≤ constant * |first - second| / scale)
    (coupling : Measure (ℝ × ℝ)) [IsFiniteMeasure coupling]
    (hcost : Integrable (fun sample : ℝ × ℝ => |sample.1 - sample.2|) coupling)
    {scale : ℝ} (hscale : 0 < scale) :
    (∫ value : ℝ, |mollifiedLaw (coupling.map Prod.fst) scale value -
      mollifiedLaw (coupling.map Prod.snd) scale value|) ≤
      constant / scale * ∫ sample : ℝ × ℝ, |sample.1 - sample.2| ∂coupling := by
  have hfirst := integrable_transportMollifier_joint coupling Prod.fst measurable_fst hscale
  have hsecond := integrable_transportMollifier_joint coupling Prod.snd measurable_snd hscale
  have hdifference := hfirst.sub hsecond
  have hidentity : (fun value : ℝ =>
      mollifiedLaw (coupling.map Prod.fst) scale value -
        mollifiedLaw (coupling.map Prod.snd) scale value) =ᵐ[volume]
      fun value => ∫ sample : ℝ × ℝ,
        transportMollifier scale (value - sample.1) -
          transportMollifier scale (value - sample.2) ∂coupling := by
    filter_upwards [hfirst.prod_left_ae, hsecond.prod_left_ae] with value hfirstValue hsecondValue
    rw [mollifiedLaw_map coupling Prod.fst measurable_fst,
      mollifiedLaw_map coupling Prod.snd measurable_snd,
      integral_sub hfirstValue hsecondValue]
  refine (integral_congr_ae (hidentity.fun_comp abs)).le.trans ?_
  calc
    _ ≤ ∫ value : ℝ, (∫ sample : ℝ × ℝ,
        |transportMollifier scale (value - sample.1) -
          transportMollifier scale (value - sample.2)| ∂coupling) := by
      apply integral_mono hdifference.integral_prod_right.abs
        (by simpa only [Pi.sub_apply, Real.norm_eq_abs] using hdifference.integral_norm_prod_right)
      intro value
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun sample : ℝ × ℝ => transportMollifier scale (value - sample.1) -
          transportMollifier scale (value - sample.2))
    _ = ∫ sample : ℝ × ℝ, (∫ value : ℝ,
        |transportMollifier scale (value - sample.1) -
          transportMollifier scale (value - sample.2)|) ∂coupling := by
      simpa only [Pi.sub_apply] using (integral_integral_swap hdifference.abs).symm
    _ ≤ ∫ sample : ℝ × ℝ, constant / scale * |sample.1 - sample.2| ∂coupling := by
      apply integral_mono
        (by simpa only [Pi.sub_apply, Real.norm_eq_abs] using hdifference.integral_norm_prod_left)
        (hcost.const_mul _)
      intro sample
      simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        htranslation scale hscale sample.1 sample.2
    _ = _ := integral_const_mul _ _

end LambdaCantor.AE
