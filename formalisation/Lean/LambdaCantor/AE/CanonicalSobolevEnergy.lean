import LambdaCantor.AE.SobolevWeightComparison
import LambdaCantor.AE.SobolevDensity
import LambdaCantor.AE.LocallyIntegrableEnergy

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal FourierTransform

namespace LambdaCantor.AE

/-- The usual inhomogeneous squared Sobolev norm, initially expressed
through the Fourier transform of the actual address measure. -/
def canonicalSobolevEnergy (ratio regularity : ℝ) : ℝ≥0∞ :=
  ∫⁻ frequency : ℝ, ENNReal.ofReal
    (Real.rpow (1 + |frequency| ^ 2) regularity *
      ‖addressFourier ratio frequency‖ ^ 4)

theorem measurable_canonicalSobolevEnergy (regularity : ℝ) :
    Measurable (fun ratio => canonicalSobolevEnergy ratio regularity) := by
  have measurable_absolute : Measurable (fun parameterAndFrequency : ℝ × ℝ =>
      |parameterAndFrequency.2|) :=
    continuous_abs.measurable.comp measurable_snd
  have hmeasurable : Measurable (fun parameterAndFrequency : ℝ × ℝ => ENNReal.ofReal
      (Real.rpow (1 + |parameterAndFrequency.2| ^ 2) regularity *
        ‖addressFourier parameterAndFrequency.1 parameterAndFrequency.2‖ ^ 4)) :=
    (((measurable_const.add (measurable_absolute.pow_const (2 : ℕ))).pow_const regularity).mul
      (measurable_joint_addressFourier.norm.pow_const (4 : ℕ))).ennreal_ofReal
  exact hmeasurable.lintegral_prod_right'

theorem canonicalSobolevEnergy_eq_convolution_energy (ratio regularity : ℝ) :
    canonicalSobolevEnergy ratio regularity =
      ∫⁻ frequency : ℝ, ENNReal.ofReal
        (Real.rpow (1 + |frequency| ^ 2) regularity *
          ‖measureFourier (selfConvolutionProbability ratio) frequency‖ ^ 2) := by
  simp only [canonicalSobolevEnergy, norm_measureFourier_selfConvolution_sq]

theorem canonicalSobolevEnergy_le_fullFourierEnergy
    (ratio : ℝ) {regularity : ℝ} (hregularity : 0 ≤ regularity) :
    canonicalSobolevEnergy ratio regularity ≤
      ENNReal.ofReal (Real.rpow (2 : ℝ) regularity) * fullFourierEnergy ratio regularity := by
  unfold canonicalSobolevEnergy fullFourierEnergy
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro frequency
  change ENNReal.ofReal (Real.rpow (1 + |frequency| ^ 2) regularity *
      ‖addressFourier ratio frequency‖ ^ 4) ≤
    ENNReal.ofReal (Real.rpow (2 : ℝ) regularity) *
      ENNReal.ofReal ((1 + Real.rpow |frequency| (2 * regularity)) *
        ‖addressFourier ratio frequency‖ ^ 4)
  have hconstant : 0 ≤ Real.rpow (2 : ℝ) regularity :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) regularity
  calc
    _ ≤ ENNReal.ofReal (Real.rpow (2 : ℝ) regularity *
        ((1 + Real.rpow |frequency| (2 * regularity)) * ‖addressFourier ratio frequency‖ ^ 4)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (Real.rpow (2 : ℝ) regularity * (1 + Real.rpow |frequency| (2 * regularity))) *
            ‖addressFourier ratio frequency‖ ^ 4 :=
          mul_le_mul_of_nonneg_right (sobolev_weight_comparison_standard_le hregularity frequency)
            (pow_nonneg (norm_nonneg _) 4)
        _ = _ := by ring
    _ = _ := ENNReal.ofReal_mul hconstant

theorem fullFourierEnergy_le_canonicalSobolevEnergy
    (ratio : ℝ) {regularity : ℝ} (hregularity : 0 ≤ regularity) :
    fullFourierEnergy ratio regularity ≤ 2 * canonicalSobolevEnergy ratio regularity := by
  have hcomparison : fullFourierEnergy ratio regularity ≤
      ENNReal.ofReal (2 : ℝ) * canonicalSobolevEnergy ratio regularity := by
    unfold canonicalSobolevEnergy fullFourierEnergy
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro frequency
    change ENNReal.ofReal ((1 + Real.rpow |frequency| (2 * regularity)) *
        ‖addressFourier ratio frequency‖ ^ 4) ≤
      ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal
        (Real.rpow (1 + |frequency| ^ 2) regularity * ‖addressFourier ratio frequency‖ ^ 4)
    calc
      _ ≤ ENNReal.ofReal (2 *
          (Real.rpow (1 + |frequency| ^ 2) regularity * ‖addressFourier ratio frequency‖ ^ 4)) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ (2 * Real.rpow (1 + |frequency| ^ 2) regularity) *
              ‖addressFourier ratio frequency‖ ^ 4 :=
            mul_le_mul_of_nonneg_right (sobolev_weight_comparison_implemented_le hregularity frequency)
              (pow_nonneg (norm_nonneg _) 4)
          _ = _ := by ring
      _ = _ := ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [ENNReal.ofReal_ofNat] using hcomparison

theorem canonicalSobolevEnergy_lt_top_of_fullFourierEnergy
    {ratio regularity : ℝ} (hregularity : 0 ≤ regularity)
    (henergy : fullFourierEnergy ratio regularity < ⊤) :
    canonicalSobolevEnergy ratio regularity < ⊤ :=
  (canonicalSobolevEnergy_le_fullFourierEnergy ratio hregularity).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top henergy)

/-- The same actual L1 and L2 density has the canonical Fourier energy.
No representative of an abstract Sobolev equivalence class is substituted. -/
theorem canonicalSobolevEnergy_eq_densityFourier
    {ratio regularity : ℝ} {density : ℝ → ℝ}
    (hintegrable : Integrable density volume)
    (hnonnegative : ∀ᵐ value : ℝ, 0 ≤ density value)
    (hmeasure : selfConvolutionProbability ratio =
      volume.withDensity (fun value => ENNReal.ofReal (density value))) :
    canonicalSobolevEnergy ratio regularity =
      ∫⁻ frequency : ℝ, ENNReal.ofReal
        (Real.rpow (1 + |frequency| ^ 2) regularity *
          ‖𝓕 (fun value => (density value : ℂ)) frequency‖ ^ 2) := by
  simp_rw [fourier_density_eq_measureFourier hintegrable.aestronglyMeasurable hnonnegative,
    ← hmeasure]
  exact canonicalSobolevEnergy_eq_convolution_energy ratio regularity

def HasCanonicalSobolevDensity (probability : Measure ℝ) (regularity : ℝ) : Prop :=
  ∃ density : ℝ → ℝ, Integrable density volume ∧ MemLp density 2 volume ∧
    (∀ᵐ value : ℝ, 0 ≤ density value) ∧
    probability = volume.withDensity (fun value => ENNReal.ofReal (density value)) ∧
    (∫⁻ frequency : ℝ, ENNReal.ofReal
      (Real.rpow (1 + |frequency| ^ 2) regularity *
        ‖𝓕 (fun value => (density value : ℂ)) frequency‖ ^ 2)) < ⊤

theorem hasCanonicalSobolevDensity_of_fullFourierEnergy
    {ratio regularity : ℝ} (hregularity : 0 ≤ regularity)
    (henergy : fullFourierEnergy ratio regularity < ⊤) :
    HasCanonicalSobolevDensity (selfConvolutionProbability ratio) regularity := by
  obtain ⟨density, hintegrable, hLp, hnonnegative, hmeasure⟩ :=
    exists_integrable_convolution_L2_density henergy
  refine ⟨density, hintegrable, hLp, hnonnegative, hmeasure, ?_⟩
  rw [← canonicalSobolevEnergy_eq_densityFourier hintegrable hnonnegative hmeasure]
  exact canonicalSobolevEnergy_lt_top_of_fullFourierEnergy hregularity henergy

theorem ae_hasCanonicalSobolevDensity_on_interval
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1) :
    ∀ᵐ ratio : ℝ, ratio ∈ Ioo lower upper →
      HasCanonicalSobolevDensity (selfConvolutionProbability ratio) regularity := by
  filter_upwards [ae_finite_fullFourierEnergy_on_interval hlower horder hupper hregularity hrange]
    with ratio hfinite
  exact fun hinside => hasCanonicalSobolevDensity_of_fullFourierEnergy hregularity (hfinite hinside)

/-- Recover the extended-valued parameter integral using the independently
proved almost-everywhere finiteness. Integrability of toReal alone would
not justify this step, since the real projection of infinity is zero. -/
theorem lintegral_fullFourierEnergy_compact_subset_lt_top
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1)
    (compact : Set ℝ) (contained : compact ⊆ Ioo lower upper) (compactness : IsCompact compact) :
    (∫⁻ ratio in compact, fullFourierEnergy ratio regularity) < ⊤ := by
  have hintegrable : IntegrableOn (fun ratio => (fullFourierEnergy ratio regularity).toReal)
      compact volume :=
    (locallyIntegrableOn_fullFourierEnergy hlower horder hupper hregularity hrange).integrableOn_compact_subset
      contained compactness
  have hfinite : ∀ᵐ ratio : ℝ ∂volume.restrict compact,
      fullFourierEnergy ratio regularity ≠ ⊤ := by
    filter_upwards [ae_restrict_of_ae
      (ae_finite_fullFourierEnergy_on_interval hlower horder hupper hregularity hrange),
      ae_restrict_mem compactness.measurableSet] with ratio hratio hinside
    exact (hratio (contained hinside)).ne
  exact lt_top_iff_ne_top.mpr ((integrable_toReal_iff
    (measurable_fullFourierEnergy regularity).aemeasurable hfinite).mp hintegrable)

/-- The canonical squared Sobolev norm has finite parameter integral on
every compact subset of the admissible interval. -/
theorem lintegral_canonicalSobolevEnergy_compact_subset_lt_top
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1)
    (compact : Set ℝ) (contained : compact ⊆ Ioo lower upper) (compactness : IsCompact compact) :
    (∫⁻ ratio in compact, canonicalSobolevEnergy ratio regularity) < ⊤ := by
  have hfull := lintegral_fullFourierEnergy_compact_subset_lt_top hlower horder hupper
    hregularity hrange compact contained compactness
  apply (lintegral_mono (fun ratio =>
    canonicalSobolevEnergy_le_fullFourierEnergy ratio hregularity)).trans_lt
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfull

theorem integrableOn_canonicalSobolevEnergy_compact_subset
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1)
    (compact : Set ℝ) (contained : compact ⊆ Ioo lower upper) (compactness : IsCompact compact) :
    IntegrableOn (fun ratio => (canonicalSobolevEnergy ratio regularity).toReal) compact volume := by
  exact integrable_toReal_of_lintegral_ne_top
    (measurable_canonicalSobolevEnergy regularity).aemeasurable
    (lintegral_canonicalSobolevEnergy_compact_subset_lt_top hlower horder hupper hregularity
      hrange compact contained compactness).ne

end LambdaCantor.AE

#print axioms LambdaCantor.AE.canonicalSobolevEnergy_le_fullFourierEnergy
#print axioms LambdaCantor.AE.fullFourierEnergy_le_canonicalSobolevEnergy
#print axioms LambdaCantor.AE.lintegral_canonicalSobolevEnergy_compact_subset_lt_top
#print axioms LambdaCantor.AE.integrableOn_canonicalSobolevEnergy_compact_subset
#print axioms LambdaCantor.AE.ae_hasCanonicalSobolevDensity_on_interval
