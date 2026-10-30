import LambdaCantor.RationalPowers.LargeExponentSource
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
namespace LambdaCantor.RationalPowers
open Integer

/-- Unlike the old integer-only transfer, a rational phase may be signed.
There is no unsupported conversion of that phase to a natural depth. -/
theorem largeExponent_phase_cover_signed_shift {ι : Type*} (valid : ι → Prop)
    (lower upper : ι → ℝ) (rotation : ℝ)
    (covered : ∀ phase ∈ Set.Icc (0 : ℝ) 1, ∃ source : ι, ∃ shift : ℤ,
      valid source ∧ lower source < phase+shift ∧ phase+shift < upper source) :
    ∃ source : ι, ∃ shift : ℤ,
      valid source ∧ lower source < rotation+shift ∧ rotation+shift < upper source := by
  obtain ⟨source,shift,source_valid,lower_bound,upper_bound⟩ := covered (Int.fract rotation)
    ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
  have identity := Int.floor_add_fract rotation
  refine ⟨source,shift-⌊rotation⌋,source_valid,?_,?_⟩ <;> push_cast <;> linarith

theorem largeExponent_centered_phase_corners
    (exponent phase center horizontalLeft horizontalRight verticalLeft verticalRight : ℝ)
    (center_positive : 0 < center) (left_positive : 0 < horizontalLeft)
    (right_positive : 0 < horizontalRight)
    (lower : (Real.log verticalLeft+exponent*Real.log (center/horizontalRight))/Real.log 3 <
      (exponent*Real.log center-Real.log exponent)/Real.log 3+phase)
    (upper : (exponent*Real.log center-Real.log exponent)/Real.log 3+phase <
      (Real.log verticalRight+exponent*Real.log (center/horizontalLeft))/Real.log 3) :
    phase*Real.log 3+exponent*Real.log horizontalLeft-Real.log exponent-Real.log verticalRight < 0 ∧
      0 < phase*Real.log 3+exponent*Real.log horizontalRight-Real.log exponent-Real.log verticalLeft := by
  have logarithm_positive : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have lower_cleared := (div_lt_iff₀ logarithm_positive).1 lower
  have upper_cleared := (lt_div_iff₀ logarithm_positive).1 upper
  rw [Real.log_div center_positive.ne' right_positive.ne'] at lower_cleared
  rw [Real.log_div center_positive.ne' left_positive.ne'] at upper_cleared
  have cancellation : ((exponent*Real.log center-Real.log exponent)/Real.log 3)*Real.log 3 =
      exponent*Real.log center-Real.log exponent := div_mul_cancel₀ _ logarithm_positive.ne'
  constructor <;> nlinarith

/-- A complete continuous phase cover supplies a phase on the actual 1/b
lattice. Its integer multiple is then realized at arbitrarily deep natural
Cantor depths by `rational_natural_phase_depths`. -/
theorem largeExponent_phase_cover_log_source
    (exponent center : ℝ) (denominator : ℕ) (denominator_positive : 0 < denominator)
    (center_positive : 0 < center)
    (covered : ∀ phase ∈ Set.Icc (0 : ℝ) 1, ∃ source : LogSourceData, ∃ shift : ℤ,
      LargeExponentGeometryChecked exponent source ∧
      largeExponentCenteredLower exponent center source < phase+shift ∧
      phase+shift < largeExponentCenteredUpper exponent center source) :
    ∃ source : LogSourceData, ∃ phaseNumerator : ℤ,
      LargeExponentGeometryChecked exponent source ∧
      ((phaseNumerator : ℝ)/denominator)*Real.log 3+
        exponent*Real.log ((source.P : ℝ)/3^source.p)-Real.log exponent-
          Real.log ((source.Q+1 : ℝ)/3^source.q) < 0 ∧
      0 < ((phaseNumerator : ℝ)/denominator)*Real.log 3+
        exponent*Real.log ((source.P+1 : ℝ)/3^source.p)-Real.log exponent-
          Real.log ((source.Q : ℝ)/3^source.q) := by
  obtain ⟨source,shift,geometry,lower,upper⟩ := largeExponent_phase_cover_signed_shift
    (LargeExponentGeometryChecked exponent) (largeExponentCenteredLower exponent center)
    (largeExponentCenteredUpper exponent center)
    ((exponent*Real.log center-Real.log exponent)/Real.log 3) covered
  have horizontal_positive : (0 : ℝ) < source.P := by exact_mod_cast geometry.1
  have corners := largeExponent_centered_phase_corners exponent (shift : ℝ) center
    ((source.P : ℝ)/3^source.p) ((source.P+1 : ℝ)/3^source.p)
    ((source.Q : ℝ)/3^source.q) ((source.Q+1 : ℝ)/3^source.q)
    center_positive (by positivity) (by positivity) lower upper
  have phase_identity : ((((denominator : ℤ)*shift : ℤ) : ℝ)/(denominator : ℝ)) = shift := by
    have denominator_nonzero : (denominator : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [denominator_nonzero]
  refine ⟨source,(denominator : ℤ)*shift,geometry,?_,?_⟩ <;>
    rw [phase_identity] <;> linarith [corners.1,corners.2]

/-- Denominator-specific modular coverage is weaker than full phase coverage
and is exactly the grouped-layer interface. A single center is fixed before
the phase cover is supplied; endpoints with different rotations cannot be
pooled. The integer phase selected here gives the actual lattice value J/b. -/
theorem largeExponent_lattice_phase_cover_log_source
    (exponent center : ℝ) (denominator : ℕ) (denominator_positive : 0 < denominator)
    (center_positive : 0 < center)
    (covered : ∀ phase ∈ Set.Icc (0 : ℝ) 1, ∃ source : LogSourceData, ∃ shift : ℤ,
      LargeExponentGeometryChecked exponent source ∧
      (denominator : ℝ)*largeExponentCenteredLower exponent center source < phase+shift ∧
      phase+shift < (denominator : ℝ)*largeExponentCenteredUpper exponent center source) :
    ∃ source : LogSourceData, ∃ phaseNumerator : ℤ,
      LargeExponentGeometryChecked exponent source ∧
      ((phaseNumerator : ℝ)/denominator)*Real.log 3+
        exponent*Real.log ((source.P : ℝ)/3^source.p)-Real.log exponent-
          Real.log ((source.Q+1 : ℝ)/3^source.q) < 0 ∧
      0 < ((phaseNumerator : ℝ)/denominator)*Real.log 3+
        exponent*Real.log ((source.P+1 : ℝ)/3^source.p)-Real.log exponent-
          Real.log ((source.Q : ℝ)/3^source.q) := by
  have denominator_real_positive : (0 : ℝ) < denominator := by exact_mod_cast denominator_positive
  obtain ⟨source,shift,geometry,lower,upper⟩ := largeExponent_phase_cover_signed_shift
    (LargeExponentGeometryChecked exponent)
    (fun source => (denominator : ℝ)*largeExponentCenteredLower exponent center source)
    (fun source => (denominator : ℝ)*largeExponentCenteredUpper exponent center source)
    ((denominator : ℝ)*((exponent*Real.log center-Real.log exponent)/Real.log 3)) covered
  have scale_identity :
      (denominator : ℝ)*((exponent*Real.log center-Real.log exponent)/Real.log 3+
        (shift : ℝ)/denominator) =
      (denominator : ℝ)*((exponent*Real.log center-Real.log exponent)/Real.log 3)+shift := by
    rw [mul_add]
    congr 1
    field_simp [denominator_real_positive.ne']
  have lower_unscaled : largeExponentCenteredLower exponent center source <
      (exponent*Real.log center-Real.log exponent)/Real.log 3+(shift : ℝ)/denominator := by
    apply (mul_lt_mul_iff_right₀ denominator_real_positive).1
    rw [scale_identity]
    exact lower
  have upper_unscaled :
      (exponent*Real.log center-Real.log exponent)/Real.log 3+(shift : ℝ)/denominator <
        largeExponentCenteredUpper exponent center source := by
    apply (mul_lt_mul_iff_right₀ denominator_real_positive).1
    rw [scale_identity]
    exact upper
  have horizontal_positive : (0 : ℝ) < source.P := by exact_mod_cast geometry.1
  have corners := largeExponent_centered_phase_corners exponent ((shift : ℝ)/denominator) center
    ((source.P : ℝ)/3^source.p) ((source.P+1 : ℝ)/3^source.p)
    ((source.Q : ℝ)/3^source.q) ((source.Q+1 : ℝ)/3^source.q)
    center_positive (by positivity) (by positivity) lower_unscaled upper_unscaled
  exact ⟨source,shift,geometry,corners.1,corners.2⟩

end LambdaCantor.RationalPowers
