import LambdaCantor.First.AddressParameter
import LambdaCantor.ParameterContinuity

noncomputable section
namespace LambdaCantor

/-- The derivative series is jointly continuous in the full address and the
parameter, uniformly up to the endpoints of a compact contraction band. -/
theorem continuous_addressParameterDerivative_band {lower upper : ℝ}
    (lower_nonnegative : 0 ≤ lower) (upper_lt_one : upper < 1)
    (ordered : lower ≤ upper) :
    Continuous (fun point : Set.Icc lower upper × (ℕ → Bool) =>
      addressParameterDerivative point.1 point.2) := by
  have upper_nonnegative : 0 ≤ upper := lower_nonnegative.trans ordered
  have digit_continuous : Continuous (fun bit : Bool => if bit then (1 : ℝ) else 0) :=
    continuous_of_discreteTopology
  have first_series : Continuous (fun point : Set.Icc lower upper × (ℕ → Bool) =>
      ∑' index : ℕ, (if point.2 index then (1 : ℝ) else 0) * (point.1 : ℝ) ^ index) := by
    apply continuous_tsum (u := fun index : ℕ => upper ^ index)
    · intro index
      exact (digit_continuous.comp ((continuous_apply index).comp continuous_snd)).mul
        ((continuous_subtype_val.comp continuous_fst).pow index)
    · exact summable_geometric_of_lt_one upper_nonnegative upper_lt_one
    · intro index point
      have parameter_nonnegative := lower_nonnegative.trans point.1.property.1
      split_ifs
      · simp only [one_mul, Real.norm_eq_abs, abs_pow, abs_of_nonneg parameter_nonnegative]
        exact pow_le_pow_left₀ parameter_nonnegative point.1.property.2 index
      · simp [pow_nonneg upper_nonnegative]
  have second_series : Continuous (fun point : Set.Icc lower upper × (ℕ → Bool) =>
      ∑' index : ℕ, (if point.2 (index + 1) then (1 : ℝ) else 0) *
        ((index : ℝ) + 1) * (point.1 : ℝ) ^ index) := by
    apply continuous_tsum (u := fun index : ℕ => ((index : ℝ) + 1) * upper ^ index)
    · intro index
      exact ((digit_continuous.comp ((continuous_apply (index + 1)).comp continuous_snd)).mul
        continuous_const).mul ((continuous_subtype_val.comp continuous_fst).pow index)
    · exact summable_address_derivative_majorant upper_nonnegative upper_lt_one
    · intro index point
      have parameter_nonnegative := lower_nonnegative.trans point.1.property.1
      split_ifs
      · simp only [one_mul, Real.norm_eq_abs]
        rw [abs_of_nonneg (mul_nonneg (by positivity) (pow_nonneg parameter_nonnegative _))]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ parameter_nonnegative point.1.property.2 index) (by positivity)
      · simp only [zero_mul, norm_zero]
        positivity
  exact first_series.neg.add
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul second_series)

end LambdaCantor
