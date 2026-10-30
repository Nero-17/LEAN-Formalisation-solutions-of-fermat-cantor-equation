import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace LambdaCantor.RationalPowers

/-- A uniform positive denominator turns simultaneous value/derivative errors
into a uniform logarithmic-derivative quotient error. -/
theorem positive_quotient_uniform_error (exponent lower epsilon : ℝ)
    (exponent_positive : 0 < exponent) (lower_positive : 0 < lower)
    (epsilon_positive : 0 < epsilon) :
    ∃ delta > 0, ∀ coordinate drop factor : ℝ,
      coordinate ∈ Set.Icc lower 1 →
      |drop-exponent*coordinate| < delta → |factor-1| < delta →
      0 < drop ∧ |exponent*factor/drop-1/coordinate| < epsilon := by
  let delta := min (exponent*lower/2) (epsilon*exponent*lower^2/(2*(exponent+1)))
  have delta_positive : 0 < delta := by dsimp [delta]; positivity
  have delta_small : delta ≤ exponent*lower/2 := min_le_left _ _
  have delta_margin : (exponent+1)*delta ≤ epsilon*exponent*lower^2/2 := by
    have bound := min_le_right (exponent*lower/2) (epsilon*exponent*lower^2/(2*(exponent+1)))
    have cleared := (le_div_iff₀ (by positivity : 0 < 2*(exponent+1))).mp bound
    change (exponent+1)*min (exponent*lower/2)
      (epsilon*exponent*lower^2/(2*(exponent+1))) ≤ epsilon*exponent*lower^2/2
    nlinarith
  refine ⟨delta, delta_positive, ?_⟩
  intro coordinate drop factor coordinate_bounds drop_error factor_error
  have coordinate_positive : 0 < coordinate := lower_positive.trans_le coordinate_bounds.1
  have drop_sides := abs_lt.mp drop_error
  have coordinate_lower := mul_le_mul_of_nonneg_left coordinate_bounds.1 exponent_positive.le
  have drop_lower : exponent*lower/2 ≤ drop := by linarith [drop_sides.1, delta_small]
  have drop_positive : 0 < drop := lt_of_lt_of_le (by positivity) drop_lower
  have denominator_lower : exponent*lower^2/2 ≤ drop*coordinate := by
    have first := mul_le_mul_of_nonneg_right drop_lower coordinate_positive.le
    have second := mul_le_mul_of_nonneg_left coordinate_bounds.1
      (show 0 ≤ exponent*lower/2 by positivity)
    nlinarith
  have denominator_positive : 0 < drop*coordinate := mul_pos drop_positive coordinate_positive
  have numerator_bound : |exponent*coordinate*(factor-1)-(drop-exponent*coordinate)| <
      (exponent+1)*delta := by
    have triangle := abs_sub (exponent*coordinate*(factor-1)) (drop-exponent*coordinate)
    rw [abs_mul, abs_of_pos (mul_pos exponent_positive coordinate_positive)] at triangle
    have factor_bound := mul_lt_mul_of_pos_left factor_error (mul_pos exponent_positive coordinate_positive)
    have coordinate_upper := mul_le_mul_of_nonneg_left coordinate_bounds.2 exponent_positive.le
    have scaled_upper := mul_le_mul_of_nonneg_right coordinate_upper delta_positive.le
    nlinarith [triangle, drop_error, factor_bound, scaled_upper]
  refine ⟨drop_positive, ?_⟩
  have identity : exponent*factor/drop-1/coordinate =
      (exponent*coordinate*(factor-1)-(drop-exponent*coordinate))/(drop*coordinate) := by
    field_simp [drop_positive.ne', coordinate_positive.ne']
    <;> ring
  rw [identity, abs_div, abs_of_pos denominator_positive]
  apply (div_lt_iff₀ denominator_positive).mpr
  have multiplied := mul_le_mul_of_nonneg_left denominator_lower epsilon_positive.le
  exact numerator_bound.trans_le (delta_margin.trans (by nlinarith [multiplied]))

end LambdaCantor.RationalPowers

