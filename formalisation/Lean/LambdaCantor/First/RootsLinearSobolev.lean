import LambdaCantor.First.RootsDensity
import LambdaCantor.First.RootsSobolev
import LambdaCantor.First.RootsConvolutionDensity
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section
open MeasureTheory
open scoped NNReal

namespace LambdaCantor.First.Roots

theorem real_density_characteristic_fourier (density : ℝ → ℝ)
    (nonnegative : ∀ point, 0 ≤ density point) (measurable : Measurable density)
    (frequency : ℝ) :
    charFun (volume.withDensity (fun point => ENNReal.ofReal (density point))) frequency =
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
        (fun point => (density point : ℂ)) (-(2 * Real.pi)⁻¹ * frequency) := by
  let nonnegativeDensity : ℝ → ℝ≥0 := fun point => ⟨density point, nonnegative point⟩
  have nonnegative_measurable : Measurable nonnegativeDensity := measurable.subtype_mk
  have density_law : volume.withDensity (fun point => (nonnegativeDensity point : ENNReal)) =
      volume.withDensity (fun point => ENNReal.ofReal (density point)) := by
    congr 1
    funext point
    exact (ENNReal.ofReal_eq_coe_nnreal (nonnegative point)).symm
  have function_identity : (fun point => nonnegativeDensity point • (1 : ℂ)) =
      (fun point => (density point : ℂ)) := by
    funext point
    rw [NNReal.smul_def]
    change density point • (1 : ℂ) = (density point : ℂ)
    rw [Complex.real_smul, mul_one]
  have identity := density_characteristic_fourier nonnegativeDensity nonnegative_measurable frequency
  rw [density_law, function_identity] at identity
  simpa only [smul_eq_mul] using identity

/-- Actual L2 densities have square-integrable characteristic functions.
The only external input is the separately sourced classical Plancherel
theorem; the conversion of conventions is explicit. -/
theorem real_density_characteristic_square_integrable (density : ℝ → ℝ)
    (nonnegative : ∀ point, 0 ≤ density point) (measurable : Measurable density)
    (integrable : Integrable density volume) (square_integrable : MemLp density 2 volume) :
    Integrable (fun frequency : ℝ =>
      ‖charFun (volume.withDensity (fun point => ENNReal.ofReal (density point))) frequency‖ ^ 2) := by
  have complex_integrable : Integrable (fun point => (density point : ℂ)) volume :=
    integrable.ofReal
  have complex_square_integrable : MemLp (fun point => (density point : ℂ)) 2 volume :=
    square_integrable.ofReal
  have fourier_square_integrable :=
    (External.classical_plancherel_l1_l2 _ complex_integrable complex_square_integrable).1
  have energy_integrable := fourier_square_integrable.integrable_norm_pow (by norm_num)
  have scale_nonzero : -(2 * Real.pi)⁻¹ ≠ 0 :=
    neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have scaled_integrable := (integrable_comp_mul_left_iff _ scale_nonzero).2 energy_integrable
  simpa only [← real_density_characteristic_fourier density nonnegative measurable] using
    scaled_integrable

/-- A probability law with an actual L2 density gains positive weighted
Fourier energy when convolved with a probability law of power Fourier decay. -/
theorem real_density_convolution_weighted_energy (measure : Measure ℝ)
    [IsProbabilityMeasure measure] (density : ℝ → ℝ)
    [IsProbabilityMeasure (volume.withDensity (fun point => ENNReal.ofReal (density point)))]
    (nonnegative : ∀ point, 0 ≤ density point) (measurable : Measurable density)
    (integrable : Integrable density volume) (square_integrable : MemLp density 2 volume)
    (order constant : ℝ) (order_pos : 0 < order) (constant_nonnegative : 0 ≤ constant)
    (decay : ∀ frequency : ℝ, 1 < |frequency| →
      ‖charFun measure frequency‖ ≤ constant * |frequency| ^ (-order)) :
    Integrable (fun frequency : ℝ => (1 + frequency ^ 2) ^ order *
      ‖charFun ((volume.withDensity (fun point => ENNReal.ofReal (density point))) ∗ measure)
        frequency‖ ^ 2) :=
  (convolution_weighted_fourier_energy _ measure order constant order_pos constant_nonnegative
    (real_density_characteristic_square_integrable density nonnegative measurable integrable
      square_integrable) decay).1

end LambdaCantor.First.Roots
