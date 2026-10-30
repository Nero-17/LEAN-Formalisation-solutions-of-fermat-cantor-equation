import LambdaCantor.First.RootsFourierCoupling
import LambdaCantor.First.RootsExternalPlancherel
import LambdaCantor.First.RootsInterpolation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace LambdaCantor.First.Roots

/-- Exact conversion of an actual density law to its Fourier integral, including
the characteristic-function sign and frequency normalization. No regularity of
the density beyond measurability is needed for this identity. -/
theorem density_characteristic_fourier (density : ℝ → ℝ≥0)
    (density_measurable : Measurable density) (frequency : ℝ) :
    charFun (volume.withDensity (fun point => (density point : ℝ≥0∞))) frequency =
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
        (fun point => density point • (1 : ℂ)) (-(2 * Real.pi)⁻¹ • frequency) := by
  rw [charFun_eq_fourierIntegral']
  unfold VectorFourier.fourierIntegral
  rw [integral_withDensity_eq_integral_smul density_measurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun point => by
    change density point • (_ • (1 : ℂ)) = _ • (density point • (1 : ℂ))
    exact smul_comm _ _ _)

/-- Density equality of a coupled law makes the preceding normalization apply
directly to the original pushforward, rather than to an unrelated Fourier model. -/
theorem mapped_density_characteristic_fourier {Ω : Type*} [MeasurableSpace Ω]
    (measure : Measure Ω) (coordinate : Ω → ℝ) (density : ℝ → ℝ≥0)
    (density_measurable : Measurable density)
    (density_law : measure.map coordinate =
      volume.withDensity (fun point => (density point : ℝ≥0∞))) (frequency : ℝ) :
    charFun (measure.map coordinate) frequency =
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
        (fun point => density point • (1 : ℂ)) (-(2 * Real.pi)⁻¹ • frequency) := by
  rw [density_law]
  exact density_characteristic_fourier density density_measurable frequency

theorem density_fourier_characteristic (density : ℝ → ℝ≥0)
    (density_measurable : Measurable density) (frequency : ℝ) :
    VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
      (fun point => density point • (1 : ℂ)) frequency =
    charFun (volume.withDensity (fun point => (density point : ℝ≥0∞)))
      (-2 * Real.pi * frequency) := by
  have normalization : -(2 * Real.pi)⁻¹ • (-2 * Real.pi * frequency) = frequency := by
    simp only [smul_eq_mul]
    field_simp [Real.pi_ne_zero] <;> ring
  rw [density_characteristic_fourier density density_measurable, normalization]

/-- The actual density Fourier transforms inherit the coupled displacement
bound, with the required 2*pi factor in the standard Fourier convention. -/
theorem density_fourier_coupling_bound {Ω : Type*} [MeasurableSpace Ω]
    (measure : Measure Ω) [IsProbabilityMeasure measure]
    (left right : Ω → ℝ) (left_measurable : Measurable left)
    (right_measurable : Measurable right) (leftDensity rightDensity : ℝ → ℝ≥0)
    (left_density_measurable : Measurable leftDensity)
    (right_density_measurable : Measurable rightDensity)
    (left_law : measure.map left = volume.withDensity (fun point => (leftDensity point : ℝ≥0∞)))
    (right_law : measure.map right = volume.withDensity (fun point => (rightDensity point : ℝ≥0∞)))
    (displacement frequency : ℝ)
    (coupling : ∀ᵐ point ∂measure, |left point - right point| ≤ displacement) :
    ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
        (fun point => leftDensity point • (1 : ℂ)) frequency -
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
        (fun point => rightDensity point • (1 : ℂ)) frequency‖ ≤
      (2 * Real.pi) * |frequency| * displacement := by
  rw [density_fourier_characteristic leftDensity left_density_measurable,
    density_fourier_characteristic rightDensity right_density_measurable,
    ← left_law, ← right_law]
  have bound := characteristic_function_coupling_bound measure left right left_measurable
    right_measurable displacement (-2 * Real.pi * frequency) coupling
  simpa [abs_mul, abs_of_pos Real.pi_pos] using bound

/-- Cauchy--Schwarz on a finite measure, in the form used on a common bounded
support of two densities. Apply with the measure restricted to that support. -/
theorem integral_norm_le_sqrt_mass_energy {Ω : Type*} [MeasurableSpace Ω]
    (measure : Measure Ω) [IsFiniteMeasure measure] (function : Ω → ℂ)
    (square_integrable : MemLp function 2 measure) :
    (∫ point, ‖function point‖ ∂measure) ≤
      Real.sqrt (measure.real Set.univ) *
        Real.sqrt (∫ point, ‖function point‖ ^ 2 ∂measure) := by
  have holder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := measure) Real.HolderConjugate.two_two
    (f := fun _ : Ω => (1 : ℝ)) (g := fun point => ‖function point‖)
    (Filter.Eventually.of_forall (fun _ => zero_le_one))
    (Filter.Eventually.of_forall (fun point => norm_nonneg (function point)))
    (by simpa using (memLp_const (μ := measure) (p := 2) (1 : ℝ)))
    (by simpa using square_integrable.norm)
  simpa only [one_mul, Real.one_rpow, integral_const, smul_eq_mul, mul_one, one_pow,
    Real.rpow_two, Real.sqrt_eq_rpow, one_div] using holder

/-- Actual supported-function L1 control by Fourier L2 energy. The only external
input is the separately documented classical L1-intersect-L2 Plancherel theorem. -/
theorem supported_l1_le_fourier_energy (function : ℝ → ℂ) (support : Set ℝ)
    [IsFiniteMeasure (volume.restrict support)]
    (integrable : Integrable function volume) (square_integrable : MemLp function 2 volume)
    (vanishes : ∀ point, point ∉ support → function point = 0) :
    (∫ point : ℝ, ‖function point‖) ≤ Real.sqrt (volume.real support) *
      Real.sqrt (∫ frequency : ℝ,
        ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
          function frequency‖ ^ 2) := by
  have bound := integral_norm_le_sqrt_mass_energy (volume.restrict support) function
    (square_integrable.restrict support)
  have norm_restriction : (∫ point in support, ‖function point‖) = ∫ point, ‖function point‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun point outside => by
      rw [vanishes point outside, norm_zero])
  have square_restriction : (∫ point in support, ‖function point‖ ^ 2) =
      ∫ point, ‖function point‖ ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun point outside => by
      rw [vanishes point outside, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)])
  rw [norm_restriction, square_restriction,
    ← (External.classical_plancherel_l1_l2 function integrable square_integrable).2] at bound
  simpa only [measureReal_def, Measure.restrict_apply_univ] using bound

/-- Quantitative L1 interpolation for an actual supported function. The
pointwise Fourier bound is supplied by the proved bounded-coupling lemma; the
weighted integral is the explicit Sobolev-energy assumption. -/
theorem supported_fourier_interpolation (function : ℝ → ℂ) (support : Set ℝ)
    [IsFiniteMeasure (volume.restrict support)]
    (integrable : Integrable function volume) (square_integrable : MemLp function 2 volume)
    (vanishes : ∀ point, point ∉ support → function point = 0)
    (displacement order constant : ℝ) (displacement_pos : 0 < displacement)
    (order_pos : 0 < order) (constant_nonnegative : 0 ≤ constant)
    (constant_large : (2 / 3 : ℝ) * (2 * Real.pi) ^ 2 ≤ constant)
    (fourier_bound : ∀ frequency : ℝ,
      ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) function frequency‖ ≤
        (2 * Real.pi * displacement) * |frequency|)
    (weighted_integrable : Integrable (fun frequency : ℝ =>
      (1 + frequency ^ 2) ^ order *
        ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) function frequency‖ ^ 2))
    (weighted_bound : (∫ frequency : ℝ, (1 + frequency ^ 2) ^ order *
      ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) function frequency‖ ^ 2) ≤
        constant) :
    (∫ point : ℝ, ‖function point‖) ≤
      Real.sqrt (volume.real support) * Real.sqrt (2 * constant) *
        displacement ^ (2 * order / (3 + 2 * order)) := by
  let transform := VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) function
  have transform_continuous : Continuous transform :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ integrable
  have energy_integrable : Integrable (fun frequency => ‖transform frequency‖ ^ 2) :=
    (External.classical_plancherel_l1_l2 function integrable square_integrable).1.integrable_norm_pow
      (by decide : (2 : ℕ) ≠ 0)
  have split_bound (radius : ℝ) (radius_pos : 0 < radius) :
      (Real.sqrt (∫ frequency : ℝ, ‖transform frequency‖ ^ 2)) ^ 2 ≤
        constant * (displacement ^ (2 : ℝ) * radius ^ (3 : ℝ) + radius ^ (-2 * order)) := by
    rw [Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]
    have low := low_frequency_linear_bound transform transform_continuous
      (2 * Real.pi * displacement) radius (by positivity) radius_pos.le fourier_bound
    have high := weighted_high_frequency_bound (fun frequency => ‖transform frequency‖ ^ 2)
      radius order radius_pos order_pos (fun _ => sq_nonneg _) energy_integrable weighted_integrable
    have complement_identity : (Set.Icc (-radius) radius)ᶜ =
        {frequency : ℝ | radius < |frequency|} := by
      ext frequency
      simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_setOf_eq, ← abs_le, not_le]
    have split := integral_add_compl (s := Set.Icc (-radius) radius)
      measurableSet_Icc energy_integrable
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -radius ≤ radius by linarith), complement_identity] at split
    rw [integral_indicator (isOpen_lt continuous_const continuous_abs).measurableSet] at high
    have low_constant : (2 / 3 : ℝ) * (2 * Real.pi * displacement) ^ 2 * radius ^ 3 ≤
        constant * (displacement ^ 2 * radius ^ 3) := by
      calc
        _ = ((2 / 3 : ℝ) * (2 * Real.pi) ^ 2) * (displacement ^ 2 * radius ^ 3) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right constant_large (by positivity)
    have high_constant := mul_le_mul_of_nonneg_left weighted_bound
      (Real.rpow_nonneg radius_pos.le (-2 * order))
    rw [← split, Real.rpow_two]
    calc
      _ ≤ constant * (displacement ^ 2 * radius ^ 3) + radius ^ (-2 * order) * constant :=
        add_le_add (low.trans low_constant) (high.trans high_constant)
      _ = _ := by
        simp only [Real.rpow_ofNat]
        ring_nf <;> rfl
  have energy_rate := fourier_interpolation_rate
    (Real.sqrt (∫ frequency : ℝ, ‖transform frequency‖ ^ 2)) constant displacement order
    constant_nonnegative displacement_pos order_pos split_bound
  calc
    _ ≤ Real.sqrt (volume.real support) *
        Real.sqrt (∫ frequency : ℝ, ‖transform frequency‖ ^ 2) :=
      supported_l1_le_fourier_energy function support integrable square_integrable vanishes
    _ ≤ Real.sqrt (volume.real support) *
        (Real.sqrt (2 * constant) * displacement ^ (2 * order / (3 + 2 * order))) :=
      mul_le_mul_of_nonneg_left energy_rate (Real.sqrt_nonneg _)
    _ = _ := by ring

end LambdaCantor.First.Roots

