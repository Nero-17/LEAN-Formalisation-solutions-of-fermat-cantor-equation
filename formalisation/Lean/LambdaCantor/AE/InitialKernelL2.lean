import LambdaCantor.AE.AffineSobolevDensity

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace LambdaCantor.AE

/-- The unweighted fourth Fourier moment scales with one inverse length,
without paying an inverse Sobolev length. This distinction is essential for
the density-point argument. -/
theorem scaled_unweighted_fourth_energy_bound (ratio : ℝ)
    {minimumScale scale regularity : ℝ}
    (minimum_positive : 0 < minimumScale) (scale_lower : minimumScale ≤ scale) :
    (∫⁻ frequency : ℝ, ENNReal.ofReal
      (‖addressFourier ratio (scale * frequency)‖ ^ 4)) ≤
        ENNReal.ofReal minimumScale⁻¹ * fullFourierEnergy ratio regularity := by
  have scaled := lintegral_comp_positive_mul
    (fun frequency => ENNReal.ofReal (‖addressFourier ratio frequency‖^4))
    (minimum_positive.trans_le scale_lower)
  rw [scaled]
  apply mul_le_mul'
    (ENNReal.ofReal_le_ofReal
      ((inv_le_inv₀ (minimum_positive.trans_le scale_lower) minimum_positive).mpr scale_lower))
  unfold fullFourierEnergy
  apply lintegral_mono
  intro frequency
  apply ENNReal.ofReal_le_ofReal
  have weight_nonnegative := Real.rpow_nonneg (abs_nonneg frequency) (2 * regularity)
  have fourth_nonnegative := pow_nonneg (norm_nonneg (addressFourier ratio frequency)) 4
  nlinarith

theorem scaledConvolution_unweighted_energy_bound (ratio : ℝ)
    {minimumScale firstScale secondScale regularity : ℝ}
    (minimum_positive : 0 < minimumScale)
    (first_lower : minimumScale ≤ firstScale) (second_lower : minimumScale ≤ secondScale) :
    (∫⁻ frequency : ℝ, ENNReal.ofReal
      (‖measureFourier (scaledConvolutionProbability ratio firstScale secondScale) frequency‖ ^ 2)) ≤
        2 * (ENNReal.ofReal minimumScale⁻¹ * fullFourierEnergy ratio regularity) := by
  have measurable_fourth (scale : ℝ) : Measurable (fun frequency : ℝ =>
      ENNReal.ofReal (‖addressFourier ratio (scale * frequency)‖ ^ 4)) :=
    ((((measurable_addressFourier ratio).comp (measurable_id.const_mul scale)).norm).pow_const 4).ennreal_ofReal
  calc
    _ ≤ ∫⁻ frequency : ℝ,
        ENNReal.ofReal (‖addressFourier ratio (firstScale * frequency)‖ ^ 4) +
          ENNReal.ofReal (‖addressFourier ratio (secondScale * frequency)‖ ^ 4) := by
      apply lintegral_mono
      intro frequency
      change ENNReal.ofReal _ ≤ ENNReal.ofReal _ + ENNReal.ofReal _
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [measureFourier_scaledConvolutionProbability, norm_mul]
      nlinarith [sq_nonneg (‖addressFourier ratio (firstScale * frequency)‖ ^ 2 -
        ‖addressFourier ratio (secondScale * frequency)‖ ^ 2)]
    _ = (∫⁻ frequency : ℝ, ENNReal.ofReal
          (‖addressFourier ratio (firstScale * frequency)‖ ^ 4)) +
        ∫⁻ frequency : ℝ, ENNReal.ofReal
          (‖addressFourier ratio (secondScale * frequency)‖ ^ 4) :=
      lintegral_add_left (measurable_fourth firstScale) _
    _ ≤ _ := by
      rw [two_mul]
      exact add_le_add
        (scaled_unweighted_fourth_energy_bound ratio minimum_positive first_lower)
        (scaled_unweighted_fourth_energy_bound ratio minimum_positive second_lower)

/-- The actual affine Newton law admits a density whose squared L2 norm has
the required one-inverse-width bound. Translation, including the Newton
constant, does not change this estimate. -/
theorem exists_affine_density_sharp_L2
    {ratio shift minimumScale firstScale secondScale regularity : ℝ}
    (minimum_positive : 0 < minimumScale)
    (first_lower : minimumScale ≤ firstScale) (second_lower : minimumScale ≤ secondScale)
    (regularity_nonnegative : 0 ≤ regularity)
    (energy_finite : fullFourierEnergy ratio regularity < ⊤) :
    ∃ density : ℝ → ℝ, Integrable density ∧ MemLp density 2 volume ∧
      (∀ᵐ value : ℝ, 0 ≤ density value) ∧
      affineConvolutionProbability ratio shift firstScale secondScale =
        volume.withDensity (fun value => ENNReal.ofReal (density value)) ∧
      ENNReal.ofReal (∫ value : ℝ, |density value| ^ 2) ≤
        2 * (ENNReal.ofReal minimumScale⁻¹ * fullFourierEnergy ratio regularity) := by
  exact classical_exists_affine_density_sharp_L2
    minimum_positive first_lower second_lower regularity_nonnegative energy_finite

end LambdaCantor.AE
