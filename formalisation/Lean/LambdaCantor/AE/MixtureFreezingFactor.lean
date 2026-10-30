import LambdaCantor.AE.FreezingSummability

noncomputable section
open scoped BigOperators

namespace LambdaCantor.AE

theorem paired_prefix_weights_sum (depth : ℕ) :
    (∑ _word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth) = 1 := by
  calc
    _ = (4 : ℝ)^depth * (1/4 : ℝ)^depth := by
      simp [Fintype.card_fun, Fintype.card_prod]
    _ = ((4 : ℝ) * (1/4 : ℝ))^depth := (mul_pow _ _ _).symm
    _ = 1 := by norm_num

/-- Exact algebraic combination of the averaged squared Sobolev bound and
the normalized transport cost. This recovers the manuscript's geometric
factor, with the required exponent one over twice one plus sigma. -/
theorem averaged_transport_freezing_factor
    {lower upper regularity : ℝ} (depth : ℕ)
    (lower_positive : 0 < lower) (upper_positive : 0 < upper)
    (regularity_positive : 0 < regularity) :
    (upper^(-(depth : ℝ) * (1 - Real.log 2 / Real.log (1/lower))))^
        (1/(2*(1+regularity))) *
      ((upper^2/lower)^depth)^(regularity/(1+regularity)) =
      freezingRatio lower upper regularity ^ depth := by
  have quotient_positive : 0 < upper^2/lower := by positivity
  have denominator_nonzero : 1 + regularity ≠ 0 := by positivity
  rw [← freezing_depth_factor lower_positive upper_positive depth,
    Real.div_rpow (Real.rpow_nonneg quotient_positive.le _)
      (Real.rpow_nonneg upper_positive.le _),
    ← Real.rpow_mul upper_positive.le,
    ← Real.rpow_natCast_mul quotient_positive.le,
    ← Real.rpow_mul quotient_positive.le,
    ← Real.rpow_mul upper_positive.le]
  have numerator_exponent :
      (depth : ℝ) * (regularity/(1+regularity)) =
        (2*regularity) * ((depth : ℝ)/(2*(1+regularity))) := by
    field_simp [denominator_nonzero]
    <;> ring
  have denominator_exponent :
      (-(depth : ℝ) * (1 - Real.log 2 / Real.log (1/lower))) *
          (1/(2*(1+regularity))) =
      -((1 - Real.log 2 / Real.log (1/lower)) *
        ((depth : ℝ)/(2*(1+regularity)))) := by ring
  rw [numerator_exponent, denominator_exponent, Real.rpow_neg upper_positive.le]
  ring

end LambdaCantor.AE
