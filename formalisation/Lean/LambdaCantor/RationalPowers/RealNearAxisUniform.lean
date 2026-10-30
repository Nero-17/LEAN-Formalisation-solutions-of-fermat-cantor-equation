import LambdaCantor.RationalPowers.RealNearAxisLog
import LambdaCantor.RationalPowers.PositiveQuotient

noncomputable section
namespace LambdaCantor.RationalPowers

def realNearAxisVertical (exponent vertical scale y : ℝ) (depth : ℕ) : ℝ :=
  (exponent/(3 : ℝ)^depth)*(1-scale*((vertical+1-y)/3^depth))^(exponent-1)/
    realPowerDrop exponent scale ((vertical+1-y)/3^depth)

/-- The exact logarithmic vertical derivative converges uniformly over the
entire source square to 1/(Q+1-y), for arbitrary real exponent > 0. This is
the real-power replacement for the integer polynomial quotient estimate. -/
theorem realNearAxisVertical_uniform (exponent vertical : ℝ) (depth : ℕ)
    (exponent_positive : 0 < exponent) (vertical_positive : 0 < vertical)
    (vertical_bound : vertical+1 ≤ (3 : ℝ)^depth)
    (epsilon : ℝ) (epsilon_positive : 0 < epsilon) :
    ∃ delta > 0, ∀ scale : ℝ, 0 < scale → scale < delta →
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        0 < realPowerDrop exponent scale ((vertical+1-y)/3^depth) ∧
        |realNearAxisVertical exponent vertical scale y depth-1/(vertical+1-y)| < epsilon := by
  have power_positive : 0 < (3 : ℝ)^depth := by positivity
  have lower_positive : 0 < vertical/(3 : ℝ)^depth := div_pos vertical_positive power_positive
  obtain ⟨quotient_error, quotient_error_positive, quotient_bound⟩ :=
    positive_quotient_uniform_error exponent (vertical/(3 : ℝ)^depth)
      (epsilon*(3 : ℝ)^depth) exponent_positive lower_positive (mul_pos epsilon_positive power_positive)
  obtain ⟨delta, delta_positive, drop_bound⟩ := realPowerDrop_uniform_positive exponent
    (vertical/(3 : ℝ)^depth) quotient_error exponent_positive lower_positive quotient_error_positive
  refine ⟨delta, delta_positive, ?_⟩
  intro scale scale_positive scale_small y y_bounds
  have coordinate_bounds : (vertical+1-y)/(3 : ℝ)^depth ∈ Set.Icc (vertical/(3 : ℝ)^depth) 1 := by
    constructor
    · apply (div_le_div_iff_of_pos_right power_positive).mpr
      linarith [y_bounds.2]
    · apply (div_le_one power_positive).mpr
      linarith [y_bounds.1, vertical_bound]
  have exact_drop := drop_bound scale scale_positive scale_small
    ((vertical+1-y)/(3 : ℝ)^depth) coordinate_bounds
  obtain ⟨drop_positive, quotient_estimate⟩ := quotient_bound
    ((vertical+1-y)/(3 : ℝ)^depth)
    (realPowerDrop exponent scale ((vertical+1-y)/(3 : ℝ)^depth))
    ((1-scale*((vertical+1-y)/(3 : ℝ)^depth))^(exponent-1))
    coordinate_bounds exact_drop.2.1 exact_drop.2.2
  refine ⟨drop_positive, ?_⟩
  have coordinate_positive : 0 < vertical+1-y := by linarith [y_bounds.2]
  have identity :
      realNearAxisVertical exponent vertical scale y depth-1/(vertical+1-y) =
      (exponent*(1-scale*((vertical+1-y)/(3 : ℝ)^depth))^(exponent-1)/
        realPowerDrop exponent scale ((vertical+1-y)/(3 : ℝ)^depth)-
          1/((vertical+1-y)/(3 : ℝ)^depth))/(3 : ℝ)^depth := by
    unfold realNearAxisVertical
    field_simp [power_positive.ne', coordinate_positive.ne', drop_positive.ne']
    <;> ring
  rw [identity, abs_div, abs_of_pos power_positive]
  exact (div_lt_iff₀ power_positive).mpr quotient_estimate

end LambdaCantor.RationalPowers

