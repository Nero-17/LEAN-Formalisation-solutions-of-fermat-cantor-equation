import LambdaCantor.AE.ClassicalDensityCore
import LambdaCantor.AE.CommonFourierBound
import LambdaCantor.AE.AffineConvolutionMeasure

noncomputable section
open MeasureTheory Filter
open scoped FourierTransform ENNReal

namespace LambdaCantor.AE

/-- Optional classical-Plancherel route to the actual complete affine
Newton density. The common Sobolev bound is still proved from the actual
Cantor Fourier energy; it is not an external parameter theorem. -/
theorem classical_exists_common_affineSobolev_density
    {ratio shift minimumScale firstScale secondScale regularity : ℝ}
    (minimum_positive : 0 < minimumScale) (first_lower : minimumScale ≤ firstScale)
    (second_lower : minimumScale ≤ secondScale) (regularity_nonnegative : 0 ≤ regularity)
    (energy_finite : fullFourierEnergy ratio regularity < ⊤) :
    ∃ density : ℝ → ℝ, Integrable density ∧ MemLp density 2 volume ∧
      (∀ᵐ point : ℝ, 0 ≤ density point) ∧
      affineConvolutionProbability ratio shift firstScale secondScale =
        volume.withDensity (fun point => ENNReal.ofReal (density point)) ∧
      (∫ point : ℝ, |density point|^2) =
        (∫ frequency : ℝ, ‖measureFourier (scaledConvolutionProbability ratio firstScale secondScale) frequency‖^2) ∧
      (∫⁻ frequency : ℝ, ENNReal.ofReal ((1+|frequency|^(2*regularity))*
        ‖𝓕 (fun point => (density point : ℂ)) frequency‖^2)) ≤
        2*(ENNReal.ofReal (1+(minimumScale^(2*regularity))⁻¹)*
          ENNReal.ofReal minimumScale⁻¹*fullFourierEnergy ratio regularity) := by
  have finite := scaledConvolutionEnergy_lt_top_of_fullEnergy minimum_positive first_lower second_lower regularity_nonnegative energy_finite
  have affine_energy :
      (∫⁻ frequency : ℝ, ENNReal.ofReal ((1+|frequency|^(2*regularity))*
        ‖measureFourier (affineConvolutionProbability ratio shift firstScale secondScale) frequency‖^2)) =
        scaledConvolutionEnergy ratio firstScale secondScale regularity := by
    simp only [norm_measureFourier_affineConvolutionProbability, scaledConvolutionEnergy]
  have fourier_integrable := classical_fourier_memLp_of_weighted_energy
    (affineConvolutionProbability ratio shift firstScale secondScale) (affine_energy.trans_lt finite)
  obtain ⟨density, integrable, square_integrable, nonnegative, law, norm_identity⟩ :=
    ExternalPlancherel.finite_measure_L2_density _ fourier_integrable
  refine ⟨density, integrable, square_integrable, nonnegative, law, ?_, ?_⟩
  · simpa only [norm_measureFourier_affineConvolutionProbability] using norm_identity
  · simp_rw [classical_fourier_density_eq_measureFourier integrable.aestronglyMeasurable nonnegative,
      ← law, norm_measureFourier_affineConvolutionProbability]
    exact common_scaledConvolution_energy_bound ratio minimum_positive first_lower second_lower regularity_nonnegative

theorem classical_unweighted_fourth_energy_scale_bound (ratio : ℝ)
    {minimumScale scale regularity : ℝ} (minimum_positive : 0 < minimumScale)
    (scale_lower : minimumScale ≤ scale) :
    (∫⁻ frequency : ℝ, ENNReal.ofReal (‖addressFourier ratio (scale*frequency)‖^4)) ≤
      ENNReal.ofReal minimumScale⁻¹*fullFourierEnergy ratio regularity := by
  have scaled := lintegral_comp_positive_mul
    (fun frequency => ENNReal.ofReal (‖addressFourier ratio frequency‖^4))
    (minimum_positive.trans_le scale_lower)
  rw [scaled]
  apply mul_le_mul'
    (ENNReal.ofReal_le_ofReal ((inv_le_inv₀ (minimum_positive.trans_le scale_lower) minimum_positive).mpr scale_lower))
  unfold fullFourierEnergy
  apply lintegral_mono
  intro frequency
  apply ENNReal.ofReal_le_ofReal
  have weight_nonnegative := Real.rpow_nonneg (abs_nonneg frequency) (2*regularity)
  nlinarith [pow_nonneg (norm_nonneg (addressFourier ratio frequency)) 4]

theorem classical_unweighted_convolution_energy_bound (ratio : ℝ)
    {minimumScale firstScale secondScale regularity : ℝ} (minimum_positive : 0 < minimumScale)
    (first_lower : minimumScale ≤ firstScale) (second_lower : minimumScale ≤ secondScale) :
    (∫⁻ frequency : ℝ, ENNReal.ofReal
      (‖measureFourier (scaledConvolutionProbability ratio firstScale secondScale) frequency‖^2)) ≤
        2*(ENNReal.ofReal minimumScale⁻¹*fullFourierEnergy ratio regularity) := by
  have measurable_fourth (scale : ℝ) : Measurable (fun frequency : ℝ =>
      ENNReal.ofReal (‖addressFourier ratio (scale*frequency)‖^4)) :=
    ((((measurable_addressFourier ratio).comp (measurable_id.const_mul scale)).norm).pow_const 4).ennreal_ofReal
  calc
    _ ≤ ∫⁻ frequency : ℝ, ENNReal.ofReal (‖addressFourier ratio (firstScale*frequency)‖^4) +
        ENNReal.ofReal (‖addressFourier ratio (secondScale*frequency)‖^4) := by
      apply lintegral_mono
      intro frequency
      change ENNReal.ofReal _ ≤ ENNReal.ofReal _ + ENNReal.ofReal _
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [measureFourier_scaledConvolutionProbability, norm_mul]
      nlinarith [sq_nonneg (‖addressFourier ratio (firstScale*frequency)‖^2-
        ‖addressFourier ratio (secondScale*frequency)‖^2)]
    _ = (∫⁻ frequency : ℝ, ENNReal.ofReal (‖addressFourier ratio (firstScale*frequency)‖^4)) +
        ∫⁻ frequency : ℝ, ENNReal.ofReal (‖addressFourier ratio (secondScale*frequency)‖^4) :=
      lintegral_add_left (measurable_fourth firstScale) _
    _ ≤ _ := by
      rw [two_mul]
      exact add_le_add
        (classical_unweighted_fourth_energy_scale_bound ratio minimum_positive first_lower)
        (classical_unweighted_fourth_energy_scale_bound ratio minimum_positive second_lower)

/-- Sharp one-inverse-width physical L2 control for the actual affine law,
with the generic classical criterion as its only added trust dependency. -/
theorem classical_exists_affine_density_sharp_L2
    {ratio shift minimumScale firstScale secondScale regularity : ℝ}
    (minimum_positive : 0 < minimumScale) (first_lower : minimumScale ≤ firstScale)
    (second_lower : minimumScale ≤ secondScale) (regularity_nonnegative : 0 ≤ regularity)
    (energy_finite : fullFourierEnergy ratio regularity < ⊤) :
    ∃ density : ℝ → ℝ, Integrable density ∧ MemLp density 2 volume ∧
      (∀ᵐ point : ℝ, 0 ≤ density point) ∧
      affineConvolutionProbability ratio shift firstScale secondScale =
        volume.withDensity (fun point => ENNReal.ofReal (density point)) ∧
      ENNReal.ofReal (∫ point : ℝ, |density point|^2) ≤
        2*(ENNReal.ofReal minimumScale⁻¹*fullFourierEnergy ratio regularity) := by
  obtain ⟨density, integrable, square_integrable, nonnegative, law, norm_identity, _⟩ :=
    classical_exists_common_affineSobolev_density (shift := shift)
      minimum_positive first_lower second_lower regularity_nonnegative energy_finite
  refine ⟨density, integrable, square_integrable, nonnegative, law, ?_⟩
  rw [norm_identity, ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm
      (classical_measurable_measureFourier (scaledConvolutionProbability ratio firstScale secondScale)).aestronglyMeasurable).mp
        (classical_fourier_memLp_of_weighted_energy (scaledConvolutionProbability ratio firstScale secondScale)
          (scaledConvolutionEnergy_lt_top_of_fullEnergy minimum_positive first_lower second_lower regularity_nonnegative energy_finite)))
      (Eventually.of_forall (fun _ => sq_nonneg _))]
  exact classical_unweighted_convolution_energy_bound ratio minimum_positive first_lower second_lower

end LambdaCantor.AE
