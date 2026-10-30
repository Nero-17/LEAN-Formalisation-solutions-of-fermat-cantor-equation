import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open MeasureTheory

namespace LambdaCantor.First.Roots

/-- The unit complex exponential is one-Lipschitz in its real phase. -/
theorem oscillation_difference_bound (left right : ℝ) :
    ‖Complex.exp (Complex.I * left) - Complex.exp (Complex.I * right)‖ ≤ |left - right| := by
  have identity : Complex.exp (Complex.I * left) - Complex.exp (Complex.I * right) =
      Complex.exp (Complex.I * right) *
        (Complex.exp (Complex.I * ((left - right : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    simp only [Complex.ofReal_sub]
    ring
  rw [identity, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

private theorem integrable_oscillation {Ω : Type*} [MeasurableSpace Ω]
    (measure : Measure Ω) [IsFiniteMeasure measure] (coordinate : Ω → ℝ)
    (coordinate_measurable : Measurable coordinate) (frequency : ℝ) :
    Integrable (fun point => Complex.exp (Complex.I *
      ((frequency * coordinate point : ℝ) : ℂ))) measure := by
  apply (integrable_const (1 : ℝ)).mono'
  · fun_prop
  · exact Filter.Eventually.of_forall (fun point =>
      (Complex.norm_exp_I_mul_ofReal (frequency * coordinate point)).le)

/-- A coupling with displacement at most t gives the genuine characteristic
function bound |hat(mu)-hat(nu)| ≤ |frequency| t. The characteristic-function
normalization is exp(i frequency x), without a 2pi factor. -/
theorem characteristic_function_coupling_bound {Ω : Type*} [MeasurableSpace Ω]
    (measure : Measure Ω) [IsProbabilityMeasure measure]
    (left right : Ω → ℝ) (left_measurable : Measurable left)
    (right_measurable : Measurable right) (displacement frequency : ℝ)
    (coupling : ∀ᵐ point ∂measure, |left point - right point| ≤ displacement) :
    ‖charFun (measure.map left) frequency - charFun (measure.map right) frequency‖ ≤
      |frequency| * displacement := by
  have left_identity : charFun (measure.map left) frequency =
      ∫ point, Complex.exp (Complex.I * ((frequency * left point : ℝ) : ℂ)) ∂measure := by
    rw [charFun_apply_real, integral_map_of_stronglyMeasurable left_measurable (by fun_prop)]
    congr 1
    funext point
    congr 1
    simp only [Complex.ofReal_mul]
    ring
  have right_identity : charFun (measure.map right) frequency =
      ∫ point, Complex.exp (Complex.I * ((frequency * right point : ℝ) : ℂ)) ∂measure := by
    rw [charFun_apply_real, integral_map_of_stronglyMeasurable right_measurable (by fun_prop)]
    congr 1
    funext point
    congr 1
    simp only [Complex.ofReal_mul]
    ring
  rw [left_identity, right_identity, ← integral_sub
    (integrable_oscillation measure left left_measurable frequency)
    (integrable_oscillation measure right right_measurable frequency)]
  have pointwise : ∀ᵐ point ∂measure,
      ‖Complex.exp (Complex.I * ((frequency * left point : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((frequency * right point : ℝ) : ℂ))‖ ≤
          |frequency| * displacement := by
    filter_upwards [coupling] with point bound
    calc
      _ ≤ |frequency * left point - frequency * right point| :=
        oscillation_difference_bound _ _
      _ = |frequency| * |left point - right point| := by rw [← mul_sub, abs_mul]
      _ ≤ |frequency| * displacement := mul_le_mul_of_nonneg_left bound (abs_nonneg _)
  simpa using norm_integral_le_of_norm_le_const pointwise

/-- The actual low-frequency squared Fourier error is at most 2 t² R³ / 3.
This supplies the low-frequency term used by the optimization theorem. -/
theorem low_frequency_coupling_bound {Ω : Type*} [MeasurableSpace Ω]
    (measure : Measure Ω) [IsProbabilityMeasure measure]
    (left right : Ω → ℝ) (left_measurable : Measurable left)
    (right_measurable : Measurable right) (displacement radius : ℝ)
    (displacement_nonnegative : 0 ≤ displacement) (radius_nonnegative : 0 ≤ radius)
    (coupling : ∀ᵐ point ∂measure, |left point - right point| ≤ displacement) :
    (∫ frequency in -radius..radius,
      ‖charFun (measure.map left) frequency - charFun (measure.map right) frequency‖ ^ 2) ≤
      (2 / 3 : ℝ) * displacement ^ 2 * radius ^ 3 := by
  have pointwise (frequency : ℝ) :
      ‖charFun (measure.map left) frequency - charFun (measure.map right) frequency‖ ^ 2 ≤
        frequency ^ 2 * displacement ^ 2 := by
    have bound := characteristic_function_coupling_bound measure left right
      left_measurable right_measurable displacement frequency coupling
    have squared := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg _) displacement_nonnegative)).2 bound
    simpa only [mul_pow, sq_abs] using squared
  have majorant_integrable : IntervalIntegrable (fun frequency : ℝ =>
      frequency ^ 2 * displacement ^ 2) volume (-radius) radius := by
    apply Continuous.intervalIntegrable
    fun_prop
  have error_integrable : IntervalIntegrable (fun frequency : ℝ =>
      ‖charFun (measure.map left) frequency - charFun (measure.map right) frequency‖ ^ 2)
        volume (-radius) radius := by
    apply IntervalIntegrable.mono_fun' majorant_integrable
    · fun_prop
    · exact Filter.Eventually.of_forall (fun frequency => by
        change ‖‖charFun (measure.map left) frequency - charFun (measure.map right) frequency‖ ^ 2‖ ≤
          frequency ^ 2 * displacement ^ 2
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg
          (‖charFun (measure.map left) frequency - charFun (measure.map right) frequency‖))]
        exact pointwise frequency)
  calc
    _ ≤ ∫ frequency in -radius..radius, frequency ^ 2 * displacement ^ 2 :=
      intervalIntegral.integral_mono_on (by linarith) error_integrable majorant_integrable
        (fun frequency _ => pointwise frequency)
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, integral_pow]
      ring

/-- Weighted Sobolev energy controls the actual high-frequency tail integral.
Apply this to the squared modulus of a Fourier transform. -/
theorem weighted_high_frequency_bound (energy : ℝ → ℝ) (radius order : ℝ)
    (radius_pos : 0 < radius) (order_pos : 0 < order)
    (energy_nonnegative : ∀ frequency, 0 ≤ energy frequency)
    (energy_integrable : Integrable energy volume)
    (weighted_integrable : Integrable
      (fun frequency => (1 + frequency ^ 2) ^ order * energy frequency) volume) :
    (∫ frequency, ({frequency : ℝ | radius < |frequency|}.indicator energy) frequency) ≤
      radius ^ (-2 * order) *
        ∫ frequency, (1 + frequency ^ 2) ^ order * energy frequency := by
  have tail_measurable : MeasurableSet {frequency : ℝ | radius < |frequency|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  calc
    _ ≤ ∫ frequency, radius ^ (-2 * order) *
        ((1 + frequency ^ 2) ^ order * energy frequency) := by
      apply integral_mono (energy_integrable.indicator tail_measurable)
        (weighted_integrable.const_mul _)
      intro frequency
      by_cases high : radius < |frequency|
      · rw [Set.indicator_of_mem
          (show frequency ∈ {frequency : ℝ | radius < |frequency|} from high)]
        have squared : radius ^ 2 ≤ 1 + frequency ^ 2 := by
          have := (sq_lt_sq₀ radius_pos.le (abs_nonneg frequency)).2 high
          rw [sq_abs] at this
          linarith
        have weight_lower : radius ^ (2 * order) ≤ (1 + frequency ^ 2) ^ order := by
          rw [Real.rpow_mul radius_pos.le, Real.rpow_two]
          exact Real.rpow_le_rpow (sq_nonneg _) squared order_pos.le
        have normalized := mul_le_mul_of_nonneg_left weight_lower
          (Real.rpow_nonneg radius_pos.le (-2 * order))
        rw [← Real.rpow_add radius_pos] at normalized
        have exponent_zero : -2 * order + 2 * order = 0 := by ring
        rw [exponent_zero, Real.rpow_zero] at normalized
        have bound := mul_le_mul_of_nonneg_right normalized (energy_nonnegative frequency)
        simpa only [one_mul, mul_assoc] using bound
      · rw [Set.indicator_of_notMem
          (show frequency ∉ {frequency : ℝ | radius < |frequency|} from high)]
        exact mul_nonneg (Real.rpow_nonneg radius_pos.le _)
          (mul_nonneg (Real.rpow_nonneg (by positivity) _) (energy_nonnegative frequency))
    _ = _ := integral_const_mul _ _

/-- The low-frequency and Sobolev tail estimates combine for the actual
characteristic functions of the coupled laws. The only analytic assumptions are
integrability of their squared difference and its Sobolev weight. -/
theorem coupled_fourier_energy_bound {Ω : Type*} [MeasurableSpace Ω]
    (measure : Measure Ω) [IsProbabilityMeasure measure]
    (left right : Ω → ℝ) (left_measurable : Measurable left)
    (right_measurable : Measurable right) (displacement radius order : ℝ)
    (displacement_nonnegative : 0 ≤ displacement) (radius_pos : 0 < radius)
    (order_pos : 0 < order)
    (coupling : ∀ᵐ point ∂measure, |left point - right point| ≤ displacement)
    (energy_integrable : Integrable (fun frequency : ℝ =>
      ‖charFun (measure.map left) frequency - charFun (measure.map right) frequency‖ ^ 2))
    (weighted_integrable : Integrable (fun frequency : ℝ =>
      (1 + frequency ^ 2) ^ order *
        ‖charFun (measure.map left) frequency - charFun (measure.map right) frequency‖ ^ 2)) :
    (∫ frequency : ℝ,
      ‖charFun (measure.map left) frequency - charFun (measure.map right) frequency‖ ^ 2) ≤
      (2 / 3 : ℝ) * displacement ^ 2 * radius ^ 3 + radius ^ (-2 * order) *
        ∫ frequency : ℝ, (1 + frequency ^ 2) ^ order *
          ‖charFun (measure.map left) frequency - charFun (measure.map right) frequency‖ ^ 2 := by
  have low := low_frequency_coupling_bound measure left right left_measurable
    right_measurable displacement radius displacement_nonnegative radius_pos.le coupling
  have high := weighted_high_frequency_bound
    (fun frequency : ℝ =>
      ‖charFun (measure.map left) frequency - charFun (measure.map right) frequency‖ ^ 2)
    radius order radius_pos order_pos (fun _ => sq_nonneg _) energy_integrable weighted_integrable
  have complement_identity : (Set.Icc (-radius) radius)ᶜ =
      {frequency : ℝ | radius < |frequency|} := by
    ext frequency
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_setOf_eq, ← abs_le, not_le]
  have split := integral_add_compl (s := Set.Icc (-radius) radius)
    measurableSet_Icc energy_integrable
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -radius ≤ radius by linarith),
    complement_identity] at split
  rw [integral_indicator (isOpen_lt continuous_const continuous_abs).measurableSet] at high
  rw [← split]
  exact add_le_add low high

theorem low_frequency_linear_bound (function : ℝ → ℂ) (continuous : Continuous function)
    (amplitude radius : ℝ) (amplitude_nonnegative : 0 ≤ amplitude)
    (radius_nonnegative : 0 ≤ radius)
    (bound : ∀ frequency, ‖function frequency‖ ≤ amplitude * |frequency|) :
    (∫ frequency in -radius..radius, ‖function frequency‖ ^ 2) ≤
      (2 / 3 : ℝ) * amplitude ^ 2 * radius ^ 3 := by
  have squared (frequency : ℝ) : ‖function frequency‖ ^ 2 ≤ amplitude ^ 2 * frequency ^ 2 := by
    have inequality := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg amplitude_nonnegative (abs_nonneg _))).2 (bound frequency)
    simpa only [mul_pow, sq_abs] using inequality
  calc
    _ ≤ ∫ frequency in -radius..radius, amplitude ^ 2 * frequency ^ 2 :=
      intervalIntegral.integral_mono_on (by linarith)
        ((continuous.norm.pow 2).intervalIntegrable _ _)
        (by apply Continuous.intervalIntegrable; fun_prop)
        (fun frequency _ => squared frequency)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      ring

/-- Separate weighted Fourier energies control the weighted energy of their
difference, including its integrability. This is the Sobolev input needed by
the combined coupling estimate. -/
theorem weighted_difference_energy (left right : ℝ → ℂ) (order : ℝ)
    (left_continuous : Continuous left) (right_continuous : Continuous right)
    (left_integrable : Integrable (fun frequency : ℝ =>
      (1 + frequency ^ 2) ^ order * ‖left frequency‖ ^ 2))
    (right_integrable : Integrable (fun frequency : ℝ =>
      (1 + frequency ^ 2) ^ order * ‖right frequency‖ ^ 2)) :
    Integrable (fun frequency : ℝ =>
      (1 + frequency ^ 2) ^ order * ‖left frequency - right frequency‖ ^ 2) ∧
    (∫ frequency : ℝ,
      (1 + frequency ^ 2) ^ order * ‖left frequency - right frequency‖ ^ 2) ≤
      2 * ((∫ frequency : ℝ, (1 + frequency ^ 2) ^ order * ‖left frequency‖ ^ 2) +
        ∫ frequency : ℝ, (1 + frequency ^ 2) ^ order * ‖right frequency‖ ^ 2) := by
  have pointwise (frequency : ℝ) :
      (1 + frequency ^ 2) ^ order * ‖left frequency - right frequency‖ ^ 2 ≤
        2 * ((1 + frequency ^ 2) ^ order * ‖left frequency‖ ^ 2 +
          (1 + frequency ^ 2) ^ order * ‖right frequency‖ ^ 2) := by
    have triangle := norm_sub_le (left frequency) (right frequency)
    have squared := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 triangle
    have square_bound : ‖left frequency - right frequency‖ ^ 2 ≤
        2 * (‖left frequency‖ ^ 2 + ‖right frequency‖ ^ 2) := by
      nlinarith [sq_nonneg (‖left frequency‖ - ‖right frequency‖)]
    have weighted := mul_le_mul_of_nonneg_left square_bound
      (Real.rpow_nonneg (show 0 ≤ 1 + frequency ^ 2 by positivity) order)
    nlinarith
  have majorant_integrable := (left_integrable.add right_integrable).const_mul (2 : ℝ)
  have difference_integrable : Integrable (fun frequency : ℝ =>
      (1 + frequency ^ 2) ^ order * ‖left frequency - right frequency‖ ^ 2) := by
    apply majorant_integrable.mono'
    · have continuous_weight : Continuous (fun frequency : ℝ => (1 + frequency ^ 2) ^ order) := by
        apply Continuous.rpow_const
        · fun_prop
        · intro frequency
          left
          positivity
      exact (continuous_weight.mul ((left_continuous.sub right_continuous).norm.pow 2)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun frequency => by
        have nonnegative : 0 ≤ (1 + frequency ^ 2) ^ order *
            ‖left frequency - right frequency‖ ^ 2 :=
          mul_nonneg (Real.rpow_nonneg (show 0 ≤ 1 + frequency ^ 2 by positivity) order)
            (sq_nonneg ‖left frequency - right frequency‖)
        simpa only [Real.norm_eq_abs, abs_of_nonneg nonnegative, Pi.add_apply] using!
          pointwise frequency)
  refine ⟨difference_integrable, ?_⟩
  calc
    _ ≤ ∫ frequency : ℝ,
        2 * ((1 + frequency ^ 2) ^ order * ‖left frequency‖ ^ 2 +
          (1 + frequency ^ 2) ^ order * ‖right frequency‖ ^ 2) :=
      integral_mono difference_integrable majorant_integrable pointwise
    _ = _ := by rw [integral_const_mul, integral_add left_integrable right_integrable]

end LambdaCantor.First.Roots

