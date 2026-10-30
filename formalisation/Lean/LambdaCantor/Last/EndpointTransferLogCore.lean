import LambdaCantor.Last.EndpointTransferPower
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

/-- A global continuous logarithm agreeing with log above a positive cutoff.
Its corner is outside the positive rectangle used by a logarithmic source. -/
def cutoffLog (cutoff value : ℝ) : ℝ := Real.log (max cutoff value)

theorem cutoffLog_continuous {cutoff : ℝ} (hpositive : 0 < cutoff) :
    Continuous (cutoffLog cutoff) := by
  exact (continuous_const.max continuous_id).log
    (fun value => ne_of_gt (hpositive.trans_le (le_max_left cutoff value)))

theorem cutoffLog_eq {cutoff value : ℝ} (hvalue : cutoff ≤ value) :
    cutoffLog cutoff value = Real.log value := by simp [cutoffLog, max_eq_right hvalue]

theorem HasStrictFDerivAt.cutoffLog
    {function : (ℝ × ℝ) → ℝ} {derivative : (ℝ × ℝ) →L[ℝ] ℝ}
    {point : ℝ × ℝ} {cutoff : ℝ}
    (hderivative : HasStrictFDerivAt function derivative point)
    (hpositive : 0 < cutoff) (hvalue : cutoff < function point) :
    HasStrictFDerivAt (fun value => cutoffLog cutoff (function value))
      ((function point)⁻¹ • derivative) point := by
  apply (hderivative.log (ne_of_gt (hpositive.trans hvalue))).congr_of_eventuallyEq
  filter_upwards [hderivative.continuousAt.eventually (lt_mem_nhds hvalue)] with value hvalue
  exact (cutoffLog_eq hvalue.le).symm

/-- Uniform denominator control for the logarithmic endpoint derivative.
Both inputs are exactly the value/partial estimates of RealPowerLimit. -/
theorem logarithmic_drop_derivative_error {exponent lower coordinate value factor epsilon : ℝ}
    (hexponent : 0 < exponent) (hlower : 0 < lower) (hcoordinate : lower ≤ coordinate)
    (hepsilon : 0 < epsilon) (hsmall : epsilon < exponent * lower / 2)
    (hvalue : |value - exponent * coordinate| < epsilon)
    (hfactor : |factor - 1| < epsilon) :
    0 < value ∧
      |exponent * factor / value - 1 / coordinate| <
        (exponent + 1 / lower) * epsilon / (exponent * lower / 2) := by
  have hcoordinate_positive : 0 < coordinate := hlower.trans_le hcoordinate
  have hdenominator : exponent * lower / 2 < value := by
    nlinarith [(abs_lt.mp hvalue).1, mul_le_mul_of_nonneg_left hcoordinate hexponent.le]
  have hvalue_positive : 0 < value := (show 0 < exponent * lower / 2 by positivity).trans hdenominator
  refine ⟨hvalue_positive, ?_⟩
  have hreciprocal : 1 / coordinate ≤ 1 / lower := one_div_le_one_div_of_le hlower hcoordinate
  have hidentity : exponent * factor / value - 1 / coordinate =
      (exponent * (factor - 1) - (value - exponent * coordinate) / coordinate) / value := by
    field_simp [hcoordinate_positive.ne', hvalue_positive.ne']
    <;> ring
  rw [hidentity, abs_div, abs_of_pos hvalue_positive]
  have htriangle : |exponent * (factor - 1) - (value - exponent * coordinate) / coordinate| <
      (exponent + 1 / lower) * epsilon := by
    apply (abs_sub _ _).trans_lt
    rw [abs_mul, abs_of_pos hexponent, abs_div, abs_of_pos hcoordinate_positive]
    have hfirst := mul_lt_mul_of_pos_left hfactor hexponent
    have hsecond : |value - exponent * coordinate| / coordinate < epsilon / lower := by
      exact (div_lt_div_of_pos_right hvalue hcoordinate_positive).trans_le
        (div_le_div_of_nonneg_left hepsilon.le hlower hcoordinate)
    convert add_lt_add hfirst hsecond using 1 <;> ring
  have hbound_positive : 0 < (exponent + 1 / lower) * epsilon := by positivity
  exact (div_lt_div_of_pos_right htriangle (by positivity)).trans
    (div_lt_div_of_pos_left hbound_positive (by positivity) hdenominator)

def powerDropQuotient (exponent scale coordinate : ℝ) : ℝ :=
  (1 - (1 - scale * coordinate) ^ exponent) / scale

def powerLogDerivative (exponent scale coordinate : ℝ) : ℝ :=
  exponent * (1 - scale * coordinate) ^ (exponent - 1) /
    powerDropQuotient exponent scale coordinate

/-- Uniform C1 convergence of the logarithmic drop on every positive fixed
coordinate interval. In particular the logarithm is defined there. -/
theorem power_log_derivative_uniform_small_scale {exponent lower epsilon : ℝ}
    (hexponent : 0 < exponent) (hlower : 0 < lower) (hepsilon : 0 < epsilon) :
    ∃ delta > 0, ∀ scale : ℝ, 0 < scale → scale < delta →
      ∀ coordinate ∈ Set.Icc lower 1,
        0 < powerDropQuotient exponent scale coordinate ∧
        |powerLogDerivative exponent scale coordinate - 1 / coordinate| < epsilon := by
  let tolerance := min (exponent * lower / 4)
    (epsilon * (exponent * lower / 2) / (2 * (exponent + 1 / lower)))
  have htolerance : 0 < tolerance := by dsimp [tolerance]; positivity
  obtain ⟨delta, hdelta, huniform⟩ := real_power_uniform_value_and_partial exponent htolerance
  refine ⟨delta, hdelta, ?_⟩
  intro scale hscale hscale_small coordinate hcoordinate
  have hunit : coordinate ∈ Set.Icc (0 : ℝ) 1 := ⟨hlower.le.trans hcoordinate.1, hcoordinate.2⟩
  have hestimates := huniform scale hscale hscale_small coordinate hunit
  have hsmall : tolerance < exponent * lower / 2 := by
    have hbound := min_le_left (exponent * lower / 4)
      (epsilon * (exponent * lower / 2) / (2 * (exponent + 1 / lower)))
    change tolerance ≤ exponent * lower / 4 at hbound
    nlinarith
  have herror := logarithmic_drop_derivative_error hexponent hlower hcoordinate.1 htolerance hsmall
    hestimates.1 hestimates.2
  refine ⟨herror.1, herror.2.trans_le ?_⟩
  have hcoefficient : 0 < exponent + 1 / lower := by positivity
  have hdenominator : 0 < exponent * lower / 2 := by positivity
  have hbound : tolerance ≤ epsilon * (exponent * lower / 2) / (2 * (exponent + 1 / lower)) :=
    min_le_right _ _
  have hbound' := (le_div_iff₀ (mul_pos (show (0 : ℝ) < 2 by norm_num) hcoefficient)).mp hbound
  rw [div_le_iff₀ hdenominator]
  nlinarith [mul_pos hepsilon hdenominator]

theorem power_log_derivative_eventually_uniform {exponent lower : ℝ}
    (hexponent : 0 < exponent) (hlower : 0 < lower) {scales : ℕ → ℝ}
    (hscales : ∀ index, 0 < scales index) (hlimit : Tendsto scales atTop (𝓝 0))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ index in atTop, ∀ coordinate ∈ Set.Icc lower 1,
      0 < powerDropQuotient exponent (scales index) coordinate ∧
      |powerLogDerivative exponent (scales index) coordinate - 1 / coordinate| < epsilon := by
  obtain ⟨delta, hdelta, huniform⟩ := power_log_derivative_uniform_small_scale hexponent hlower hepsilon
  filter_upwards [hlimit.eventually (gt_mem_nhds hdelta)] with index hsmall
  exact huniform (scales index) (hscales index) hsmall

end LambdaCantor.Last
