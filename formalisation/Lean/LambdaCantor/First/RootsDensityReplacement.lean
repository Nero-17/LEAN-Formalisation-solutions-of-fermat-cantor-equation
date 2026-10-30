import LambdaCantor.First.RootsDensityEnergyReal

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

/-- Actual coupled probability laws with supported L2 densities and bounded
characteristic Sobolev energies satisfy the quantitative L1 replacement rate.
This theorem connects the law, density and Fourier estimates explicitly. -/
theorem coupled_supported_density_l1_bound {Source : Type*} [MeasurableSpace Source]
    (source : Measure Source) [IsProbabilityMeasure source]
    (leftCoordinate rightCoordinate : Source → ℝ)
    (left_coordinate_measurable : Measurable leftCoordinate)
    (right_coordinate_measurable : Measurable rightCoordinate)
    (leftDensity rightDensity : ℝ → ℝ)
    (left_nonnegative : ∀ point, 0 ≤ leftDensity point)
    (right_nonnegative : ∀ point, 0 ≤ rightDensity point)
    (left_measurable : Measurable leftDensity) (right_measurable : Measurable rightDensity)
    (left_integrable : Integrable leftDensity volume) (right_integrable : Integrable rightDensity volume)
    (left_square : MemLp leftDensity 2 volume) (right_square : MemLp rightDensity 2 volume)
    (left_law : source.map leftCoordinate = volume.withDensity (fun point => ENNReal.ofReal (leftDensity point)))
    (right_law : source.map rightCoordinate = volume.withDensity (fun point => ENNReal.ofReal (rightDensity point)))
    (support : Set ℝ) [IsFiniteMeasure (volume.restrict support)]
    (left_support : ∀ point, point ∉ support → leftDensity point = 0)
    (right_support : ∀ point, point ∉ support → rightDensity point = 0)
    (displacement order energyBound constant : ℝ)
    (displacement_positive : 0 < displacement) (order_positive : 0 < order)
    (energy_nonnegative : 0 ≤ energyBound) (constant_nonnegative : 0 ≤ constant)
    (constant_low : (2 / 3 : ℝ) * (2 * Real.pi) ^ 2 ≤ constant)
    (constant_energy : 4 * (2 : ℝ) ^ order * energyBound ≤ constant)
    (left_energy : (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ order *
      ‖charFun (source.map leftCoordinate) frequency‖ ^ 2)) ≤ ENNReal.ofReal energyBound)
    (right_energy : (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ order *
      ‖charFun (source.map rightCoordinate) frequency‖ ^ 2)) ≤ ENNReal.ofReal energyBound)
    (coupling : ∀ᵐ point ∂source, |leftCoordinate point - rightCoordinate point| ≤ displacement) :
    (∫ point : ℝ, |leftDensity point - rightDensity point|) ≤
      Real.sqrt (volume.real support) * Real.sqrt (2 * constant) *
        displacement ^ (2 * order / (3 + 2 * order)) := by
  have left_fourier_integrable := density_fourier_weighted_integrable (source.map leftCoordinate)
    leftDensity left_nonnegative left_measurable left_law order order_positive.le
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top left_energy)
  have right_fourier_integrable := density_fourier_weighted_integrable (source.map rightCoordinate)
    rightDensity right_nonnegative right_measurable right_law order order_positive.le
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top right_energy)
  have difference_energy := weighted_difference_energy
    (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) (fun point => (leftDensity point : ℂ)))
    (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) (fun point => (rightDensity point : ℂ))) order
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ left_integrable.ofReal)
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ right_integrable.ofReal)
    left_fourier_integrable right_fourier_integrable
  have left_bound := density_fourier_weighted_real_bound (source.map leftCoordinate)
    leftDensity left_nonnegative left_measurable left_law order energyBound order_positive.le energy_nonnegative left_energy
  have right_bound := density_fourier_weighted_real_bound (source.map rightCoordinate)
    rightDensity right_nonnegative right_measurable right_law order energyBound order_positive.le energy_nonnegative right_energy
  have estimate := supported_fourier_interpolation
    (fun point => (leftDensity point : ℂ) - (rightDensity point : ℂ)) support
    (left_integrable.ofReal.sub right_integrable.ofReal) (left_square.ofReal.sub right_square.ofReal)
    (fun point outside => by rw [left_support point outside, right_support point outside]; simp)
    displacement order constant displacement_positive order_positive constant_nonnegative constant_low
    (by
      intro frequency
      rw [density_difference_fourier leftDensity rightDensity left_integrable right_integrable,
        real_density_fourier_characteristic (source.map leftCoordinate) leftDensity left_nonnegative left_measurable left_law,
        real_density_fourier_characteristic (source.map rightCoordinate) rightDensity right_nonnegative right_measurable right_law]
      have estimate := characteristic_function_coupling_bound source leftCoordinate rightCoordinate
        left_coordinate_measurable right_coordinate_measurable displacement (-2 * Real.pi * frequency) coupling
      simpa [abs_mul, abs_of_pos Real.pi_pos, mul_assoc, mul_left_comm, mul_comm] using estimate)
    (by
      simp_rw [density_difference_fourier leftDensity rightDensity left_integrable right_integrable]
      exact difference_energy.1)
    (by
      simp_rw [density_difference_fourier leftDensity rightDensity left_integrable right_integrable]
      have bound := difference_energy.2
      nlinarith)
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using estimate

end LambdaCantor.First.Roots
