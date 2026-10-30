import LambdaCantor.Last.RealPowerLimit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.RationalPowers

/-- Exact divided real-power drop on an actual positive near-axis scale. -/
def realPowerDrop (exponent scale coordinate : ℝ) : ℝ :=
  (1-(1-scale*coordinate)^exponent)/scale

def realNearAxisLog (exponent phase : ℝ) (horizontalDepth verticalDepth : ℕ)
    (horizontal vertical scale x y : ℝ) : ℝ :=
  phase*Real.log 3+exponent*Real.log ((horizontal+x)/3^horizontalDepth)-
    Real.log (realPowerDrop exponent scale ((vertical+1-y)/3^verticalDepth))

theorem realPowerDrop_limit (exponent coordinate : ℝ) :
    Tendsto (fun scale => realPowerDrop exponent scale coordinate) (𝓝[>] 0)
      (𝓝 (exponent*coordinate)) :=
  Last.real_power_drop_limit exponent coordinate

theorem realPowerDrop_hasDerivAt {exponent scale : ℝ}
    (exponent_ge_one : 1 ≤ exponent) (scale_nonzero : scale ≠ 0) (coordinate : ℝ) :
    HasDerivAt (realPowerDrop exponent scale)
      (exponent*(1-scale*coordinate)^(exponent-1)) coordinate := by
  have derivative := (((((hasDerivAt_id coordinate).const_mul scale).const_sub 1).rpow_const
    (p := exponent) (Or.inr exponent_ge_one)).const_sub 1).div_const scale
  convert! derivative using 1 <;> simp only [realPowerDrop, id_eq, mul_one]
  all_goals first
    | (funext value <;> ring)
    | (field_simp [scale_nonzero] <;> ring)

theorem continuous_realPowerDrop {exponent : ℝ} (exponent_ge_one : 1 ≤ exponent) (scale : ℝ) :
    Continuous (realPowerDrop exponent scale) := by
  unfold realPowerDrop
  exact (continuous_const.sub
    ((continuous_const.sub (continuous_const.mul continuous_id)).rpow_const
      (fun _ => Or.inr (by linarith)))).div_const scale

theorem realNearAxisLog_horizontal_derivative {exponent phase : ℝ}
    (horizontalDepth verticalDepth : ℕ) (horizontal vertical scale x y : ℝ)
    (horizontal_positive : 0 < horizontal+x) :
    HasDerivAt
      (fun coordinate => realNearAxisLog exponent phase horizontalDepth verticalDepth
        horizontal vertical scale coordinate y) (exponent/(horizontal+x)) x := by
  have inner_derivative := ((hasDerivAt_id x).const_add horizontal).div_const ((3 : ℝ)^horizontalDepth)
  have positive : 0 < (horizontal+x)/(3 : ℝ)^horizontalDepth := by positivity
  have derivative := (((inner_derivative.log positive.ne').const_mul exponent).const_add
    (phase*Real.log 3)).sub_const
      (Real.log (realPowerDrop exponent scale ((vertical+1-y)/3^verticalDepth)))
  convert! derivative using 1 <;> simp only [realNearAxisLog, id_eq]
  all_goals first
    | (funext value <;> ring)
    | (field_simp [horizontal_positive.ne'] <;> ring)

theorem realNearAxisLog_vertical_derivative {exponent phase scale : ℝ}
    (exponent_ge_one : 1 ≤ exponent) (scale_nonzero : scale ≠ 0)
    (horizontalDepth verticalDepth : ℕ) (horizontal vertical x y : ℝ)
    (drop_positive : 0 < realPowerDrop exponent scale ((vertical+1-y)/3^verticalDepth)) :
    HasDerivAt
      (fun coordinate => realNearAxisLog exponent phase horizontalDepth verticalDepth
        horizontal vertical scale x coordinate)
      ((exponent/(3 : ℝ)^verticalDepth)*
        (1-scale*((vertical+1-y)/3^verticalDepth))^(exponent-1)/
          realPowerDrop exponent scale ((vertical+1-y)/3^verticalDepth)) y := by
  have coordinate_derivative := ((hasDerivAt_id y).const_sub (vertical+1)).div_const ((3 : ℝ)^verticalDepth)
  have drop_derivative := (realPowerDrop_hasDerivAt exponent_ge_one scale_nonzero
    ((vertical+1-y)/3^verticalDepth)).comp y coordinate_derivative
  have derivative := (drop_derivative.log drop_positive.ne').const_sub
    (phase*Real.log 3+exponent*Real.log ((horizontal+x)/3^horizontalDepth))
  convert! derivative using 1 <;> simp only [realNearAxisLog, id_eq, Function.comp_apply]
  all_goals first
    | (funext value <;> ring)
    | ring

/-- Real exponent C0 logarithmic source limit at any positive fixed corner.
The derivative formulas above identify the exact C1 quantities required for
the uniform-on-rectangle upgrade. -/
theorem realNearAxisLog_limit (exponent phase : ℝ) (exponent_positive : 0 < exponent)
    (horizontalDepth verticalDepth : ℕ) (horizontal vertical x y : ℝ)
    (vertical_positive : 0 < vertical+1-y) :
    Tendsto (fun scale => realNearAxisLog exponent phase horizontalDepth verticalDepth
      horizontal vertical scale x y) (𝓝[>] 0)
      (𝓝 (phase*Real.log 3+exponent*Real.log ((horizontal+x)/3^horizontalDepth)-
        Real.log exponent-Real.log ((vertical+1-y)/3^verticalDepth))) := by
  have coordinate_positive : 0 < (vertical+1-y)/(3 : ℝ)^verticalDepth := by positivity
  have drop_limit := realPowerDrop_limit exponent ((vertical+1-y)/3^verticalDepth)
  have logarithm_limit := (Real.continuousAt_log (mul_pos exponent_positive coordinate_positive).ne').tendsto.comp
    drop_limit
  have combined : Tendsto
      (fun scale => phase*Real.log 3+exponent*Real.log ((horizontal+x)/3^horizontalDepth)-
        Real.log (realPowerDrop exponent scale ((vertical+1-y)/3^verticalDepth)))
      (𝓝[>] 0) (𝓝 (phase*Real.log 3+exponent*Real.log ((horizontal+x)/3^horizontalDepth)-
        Real.log (exponent*((vertical+1-y)/3^verticalDepth)))) :=
    tendsto_const_nhds.sub logarithm_limit
  have identity : phase*Real.log 3+exponent*Real.log ((horizontal+x)/3^horizontalDepth)-
      Real.log (exponent*((vertical+1-y)/3^verticalDepth)) =
      phase*Real.log 3+exponent*Real.log ((horizontal+x)/3^horizontalDepth)-
        Real.log exponent-Real.log ((vertical+1-y)/3^verticalDepth) := by
    rw [Real.log_mul exponent_positive.ne' coordinate_positive.ne']
    ring
  simpa only [realNearAxisLog, identity] using combined

/-- Uniform value/partial control on a positive source interval, with
positivity of the exact divided residual included. This is the noninteger
replacement for positivity of the polynomial Fermat quotient. -/
theorem realPowerDrop_uniform_positive (exponent lower epsilon : ℝ)
    (exponent_positive : 0 < exponent) (lower_positive : 0 < lower)
    (epsilon_positive : 0 < epsilon) :
    ∃ delta > 0, ∀ scale : ℝ, 0 < scale → scale < delta →
      ∀ coordinate ∈ Set.Icc lower 1,
        0 < realPowerDrop exponent scale coordinate ∧
        |realPowerDrop exponent scale coordinate-exponent*coordinate| < epsilon ∧
        |(1-scale*coordinate)^(exponent-1)-1| < epsilon := by
  obtain ⟨delta, delta_positive, estimate⟩ := Last.real_power_uniform_value_and_partial exponent
    (lt_min epsilon_positive (by positivity : 0 < exponent*lower/2))
  refine ⟨delta, delta_positive, ?_⟩
  intro scale scale_positive scale_small coordinate coordinate_bounds
  have bounds := estimate scale scale_positive scale_small coordinate
    ⟨lower_positive.le.trans coordinate_bounds.1, coordinate_bounds.2⟩
  have value_error : |realPowerDrop exponent scale coordinate-exponent*coordinate| <
      min epsilon (exponent*lower/2) := bounds.1
  have value_sides := abs_lt.mp value_error
  have lower_product := mul_le_mul_of_nonneg_left coordinate_bounds.1 exponent_positive.le
  have small_error := min_le_right epsilon (exponent*lower/2)
  exact ⟨by nlinarith [value_sides.1], value_error.trans_le (min_le_left _ _),
    bounds.2.trans_le (min_le_left _ _)⟩

/-- A zero of the exact real logarithmic source is a zero of the original
Fermat equation at the actual natural Cantor depths. The rational phase
sequence in PhaseDepths supplies precisely the displayed depth relation. -/
theorem realNearAxisLog_zero_physical_equation
    (exponent phase : ℝ) (horizontalDepth verticalDepth firstDepth secondDepth : ℕ)
    (horizontal vertical x y : ℝ)
    (phase_relation : phase = (secondDepth : ℝ)-exponent*firstDepth)
    (horizontal_positive : 0 < (horizontal+x)/(3 : ℝ)^horizontalDepth)
    (drop_positive : 0 < realPowerDrop exponent ((1/3 : ℝ)^secondDepth)
      ((vertical+1-y)/(3 : ℝ)^verticalDepth))
    (zero : realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical
      ((1/3 : ℝ)^secondDepth) x y = 0) :
    ((1/3 : ℝ)^firstDepth*((horizontal+x)/(3 : ℝ)^horizontalDepth))^exponent+
      (1-(1/3 : ℝ)^secondDepth*((vertical+1-y)/(3 : ℝ)^verticalDepth))^exponent = 1 := by
  have first_scale_positive : 0 < (1/3 : ℝ)^firstDepth := by positivity
  have second_scale_positive : 0 < (1/3 : ℝ)^secondDepth := by positivity
  have log_ratio : Real.log (1/3 : ℝ) = -Real.log 3 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0), Real.log_one]
    ring
  have power_identity :
      ((1/3 : ℝ)^firstDepth*((horizontal+x)/(3 : ℝ)^horizontalDepth))^exponent =
      (1/3 : ℝ)^secondDepth*
        realPowerDrop exponent ((1/3 : ℝ)^secondDepth) ((vertical+1-y)/(3 : ℝ)^verticalDepth) := by
    apply Real.log_injOn_pos (Real.rpow_pos_of_pos (mul_pos first_scale_positive horizontal_positive) _)
      (mul_pos second_scale_positive drop_positive)
    rw [Real.log_rpow (mul_pos first_scale_positive horizontal_positive),
      Real.log_mul first_scale_positive.ne' horizontal_positive.ne',
      Real.log_mul second_scale_positive.ne' drop_positive.ne', Real.log_pow, Real.log_pow, log_ratio]
    unfold realNearAxisLog at zero
    rw [phase_relation] at zero
    nlinarith [zero]
  have drop_identity :
      (1/3 : ℝ)^secondDepth*
        realPowerDrop exponent ((1/3 : ℝ)^secondDepth) ((vertical+1-y)/(3 : ℝ)^verticalDepth) =
      1-(1-(1/3 : ℝ)^secondDepth*((vertical+1-y)/(3 : ℝ)^verticalDepth))^exponent := by
    unfold realPowerDrop
    field_simp [second_scale_positive.ne']
  rw [drop_identity] at power_identity
  nlinarith [power_identity]

end LambdaCantor.RationalPowers

