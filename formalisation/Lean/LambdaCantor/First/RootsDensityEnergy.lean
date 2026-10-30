import LambdaCantor.First.RootsAffineEnergy
import LambdaCantor.First.RootsDensity
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LambdaCantor.First.Roots

theorem real_density_fourier_characteristic (measure : Measure ℝ) (density : ℝ → ℝ)
    (nonnegative : ∀ point, 0 ≤ density point) (measurable : Measurable density)
    (law : measure = volume.withDensity (fun point => ENNReal.ofReal (density point))) (frequency : ℝ) :
    VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
      (fun point => (density point : ℂ)) frequency = charFun measure (-2 * Real.pi * frequency) := by
  rw [law]
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
  have identity := density_fourier_characteristic nonnegativeDensity nonnegative_measurable frequency
  rw [density_law, function_identity] at identity
  exact identity

/-- Conversion from actual characteristic energy to density Fourier energy,
with the full 2*pi frequency normalization retained. -/
theorem density_fourier_weighted_energy_bound (measure : Measure ℝ) [IsFiniteMeasure measure]
    (density : ℝ → ℝ) (nonnegative : ∀ point, 0 ≤ density point) (measurable : Measurable density)
    (law : measure = volume.withDensity (fun point => ENNReal.ofReal (density point)))
    (order : ℝ) (order_nonnegative : 0 ≤ order) :
    (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ order *
      ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
        (fun point => (density point : ℂ)) frequency‖ ^ 2)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ order) *
        (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ order * ‖charFun measure frequency‖ ^ 2)) := by
  have scale_bound : (1 : ℝ) ≤ |-2 * Real.pi| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    norm_num
    linarith [Real.two_le_pi]
  have bound := affine_characteristic_energy_bound measure 0 (-2 * Real.pi) 1 order
    zero_lt_one scale_bound order_nonnegative
  have two_identity : (1 : ℝ) + 1 = 2 := by norm_num
  simp only [norm_charFun_affine, inv_one, one_pow, two_identity, ENNReal.ofReal_one, mul_one] at bound
  simpa only [real_density_fourier_characteristic measure density nonnegative measurable law] using bound

/-- Finite actual characteristic energy yields the real weighted Fourier
integrability required by the already formalized density interpolation. -/
theorem density_fourier_weighted_integrable (measure : Measure ℝ) [IsFiniteMeasure measure]
    (density : ℝ → ℝ) (nonnegative : ∀ point, 0 ≤ density point) (measurable : Measurable density)
    (law : measure = volume.withDensity (fun point => ENNReal.ofReal (density point)))
    (order : ℝ) (order_nonnegative : 0 ≤ order)
    (finite_energy : (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ order *
      ‖charFun measure frequency‖ ^ 2)) ≠ ∞) :
    Integrable (fun frequency : ℝ => (1 + frequency ^ 2) ^ order *
      ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
        (fun point => (density point : ℂ)) frequency‖ ^ 2) volume := by
  have bound := density_fourier_weighted_energy_bound measure density nonnegative measurable law order order_nonnegative
  constructor
  · simp_rw [real_density_fourier_characteristic measure density nonnegative measurable law]
    exact (show Measurable (fun frequency : ℝ => (1 + frequency ^ 2) ^ order *
      ‖charFun measure (-2 * Real.pi * frequency)‖ ^ 2) by fun_prop).aestronglyMeasurable
  · apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun frequency =>
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)))).2
    exact bound.trans_lt (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top finite_energy))

end LambdaCantor.First.Roots
