import LambdaCantor.AE.SobolevTransportSupport
import LambdaCantor.AE.SobolevTransportCoupling

noncomputable section
open Set MeasureTheory Convolution Filter
open scoped FourierTransform ENNReal

namespace LambdaCantor.AE

theorem mollifyDensity_eq_mollifiedLaw {density : ℝ → ℝ}
    (hmeasurable : AEStronglyMeasurable density volume)
    (hnonnegative : ∀ᵐ value : ℝ, 0 ≤ density value) (scale value : ℝ) :
    mollifyDensity density scale value =
      mollifiedLaw (volume.withDensity (fun location => ENNReal.ofReal (density location)))
        scale value := by
  rw [mollifiedLaw, integral_withDensity_eq_integral_toReal_smul₀
    hmeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall (fun location => ENNReal.ofReal_lt_top))]
  unfold mollifyDensity
  rw [convolution_def]
  apply integral_congr_ae
  filter_upwards [hnonnegative] with location hlocation
  change density location * transportMollifier scale (value - location) =
    (ENNReal.ofReal (density location)).toReal * transportMollifier scale (value - location)
  rw [ENNReal.toReal_ofReal hlocation]

theorem density_L1_triangle_through_mollification {first second : ℝ → ℝ}
    (hfirst : Integrable first) (hsecond : Integrable second)
    {scale : ℝ} (hscale : 0 < scale) :
    (∫ value : ℝ, |first value - second value|) ≤
      (∫ value : ℝ, |first value - mollifyDensity first scale value|) +
      (∫ value : ℝ, |mollifyDensity first scale value - mollifyDensity second scale value|) +
      (∫ value : ℝ, |second value - mollifyDensity second scale value|) := by
  have hmfirst := integrable_mollifyDensity hfirst hscale
  have hmsecond := integrable_mollifyDensity hsecond hscale
  change (∫ value : ℝ, |(first - second) value|) ≤
    (∫ value : ℝ, |(first - mollifyDensity first scale) value|) +
    (∫ value : ℝ, |(mollifyDensity first scale - mollifyDensity second scale) value|) +
    (∫ value : ℝ, |(second - mollifyDensity second scale) value|)
  refine (integral_mono (hfirst.sub hsecond).abs
    (((hfirst.sub hmfirst).abs.add (hmfirst.sub hmsecond).abs).add
      (hsecond.sub hmsecond).abs) ?_).trans_eq ?_
  · intro value
    calc
      _ ≤ |first value - mollifyDensity first scale value| +
          |mollifyDensity first scale value - second value| := abs_sub_le _ _ _
      _ ≤ _ := by
        have htriangle := abs_sub_le (mollifyDensity first scale value)
          (mollifyDensity second scale value) (second value)
        rw [abs_sub_comm (mollifyDensity second scale value) (second value)] at htriangle
        simpa only [Pi.add_apply, Pi.sub_apply, add_assoc] using
          add_le_add (le_refl |first value - mollifyDensity first scale value|) htriangle
  · exact (integral_add
      ((hfirst.sub hmfirst).abs.add (hmfirst.sub hmsecond).abs)
      (hsecond.sub hmsecond).abs).trans
        (congrArg (fun total : ℝ => total +
          ∫ value : ℝ, |(second - mollifyDensity second scale) value|)
          (integral_add (hfirst.sub hmfirst).abs (hmfirst.sub hmsecond).abs))

/-- The two smoothing errors and the actual common-law coupling estimate.
All Fourier energies and marginal identities refer to the given densities. -/
theorem density_L1_smoothing_coupling_bound
    {first second : ℝ → ℝ} {radius scale regularity bound constant : ℝ}
    (hfirst : Integrable first) (hsecond : Integrable second)
    (hfirstNonnegative : ∀ᵐ value : ℝ, 0 ≤ first value)
    (hsecondNonnegative : ∀ᵐ value : ℝ, 0 ≤ second value)
    (hradius : 0 ≤ radius) (hscale : 0 < scale) (hscaleOne : scale ≤ 1)
    (hregularity : 0 ≤ regularity) (hregularityOne : regularity ≤ 1)
    (hbound : 0 ≤ bound)
    (hfirstSupport : Function.support first ⊆ Icc (-radius) radius)
    (hsecondSupport : Function.support second ⊆ Icc (-radius) radius)
    (hfirstEnergy : (∫⁻ frequency : ℝ, ENNReal.ofReal
      ((1 + |frequency| ^ (2 * regularity)) *
        ‖𝓕 (fun value => (first value : ℂ)) frequency‖ ^ 2)) ≤ ENNReal.ofReal (bound ^ 2))
    (hsecondEnergy : (∫⁻ frequency : ℝ, ENNReal.ofReal
      ((1 + |frequency| ^ (2 * regularity)) *
        ‖𝓕 (fun value => (second value : ℂ)) frequency‖ ^ 2)) ≤ ENNReal.ofReal (bound ^ 2))
    (htranslation : ∀ scale : ℝ, 0 < scale → ∀ first second : ℝ,
      (∫ value : ℝ, |transportMollifier scale (value - first) -
        transportMollifier scale (value - second)|) ≤ constant * |first - second| / scale)
    (coupling : Measure (ℝ × ℝ)) [IsFiniteMeasure coupling]
    (hcost : Integrable (fun sample : ℝ × ℝ => |sample.1 - sample.2|) coupling)
    (hfirstLaw : coupling.map Prod.fst =
      volume.withDensity (fun value => ENNReal.ofReal (first value)))
    (hsecondLaw : coupling.map Prod.snd =
      volume.withDensity (fun value => ENNReal.ofReal (second value))) :
    (∫ value : ℝ, |first value - second value|) ≤
      (2 * Real.sqrt (2 * (radius + 1)) * (2 * Real.pi + 2)) *
        bound * scale ^ regularity +
      constant / scale * ∫ sample : ℝ × ℝ, |sample.1 - sample.2| ∂coupling := by
  have hfirstError := mollification_L1_error_bound hfirst hradius hscale hscaleOne
    hregularity hregularityOne hbound hfirstSupport hfirstEnergy
  have hsecondError := mollification_L1_error_bound hsecond hradius hscale hscaleOne
    hregularity hregularityOne hbound hsecondSupport hsecondEnergy
  have hmiddle := mollifiedLaw_L1_le_coupling_cost htranslation coupling hcost hscale
  rw [hfirstLaw, hsecondLaw] at hmiddle
  simp_rw [← mollifyDensity_eq_mollifiedLaw hfirst.aestronglyMeasurable hfirstNonnegative,
    ← mollifyDensity_eq_mollifiedLaw hsecond.aestronglyMeasurable hsecondNonnegative] at hmiddle
  have htriangle := density_L1_triangle_through_mollification hfirst hsecond hscale
  nlinarith

end LambdaCantor.AE
