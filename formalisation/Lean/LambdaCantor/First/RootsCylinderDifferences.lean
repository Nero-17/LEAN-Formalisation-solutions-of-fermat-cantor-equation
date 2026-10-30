import LambdaCantor.First.RootsResidualEstimates
import LambdaCantor.First.AddressSecondParameter

noncomputable section
namespace LambdaCantor.First.Roots

theorem cylinderDigits_shared_prefix (word : ℕ → Bool) (length depth : ℕ)
    (left right : ℕ → Bool) (agreement : ∀ index < depth, left index = right index) :
    ∀ index < length + depth, cylinderDigits word length left index = cylinderDigits word length right index := by
  intro index index_lt
  unfold cylinderDigits
  split_ifs with before
  · rfl
  · exact agreement (index - length) (by omega)

/-- Shared-prefix parameter derivatives for the actual cylinder coordinates,
including the fixed initial word length. -/
theorem cylinderCoordinate_shared_prefix_derivative_bound {ratio upper : ℝ}
    (positive : 0 < ratio) (ratio_le_upper : ratio ≤ upper) (upper_lt_one : upper < 1)
    (word : ℕ → Bool) (length depth : ℕ) (left right : ℕ → Bool)
    (agreement : ∀ index < depth, left index = right index) :
    |deriv (cylinderCoordinate word length left) ratio - deriv (cylinderCoordinate word length right) ratio| ≤
      ((length + depth : ℕ) : ℝ) * ratio ^ (length + depth - 1) +
        2 * addressParameterDerivativeBound upper * ratio ^ (length + depth) := by
  rw [(hasDerivAt_cylinderCoordinate positive (ratio_le_upper.trans_lt upper_lt_one) word length left).deriv,
    (hasDerivAt_cylinderCoordinate positive (ratio_le_upper.trans_lt upper_lt_one) word length right).deriv]
  exact address_shared_prefix_derivative_bound positive ratio_le_upper upper_lt_one
    (cylinderDigits word length left) (cylinderDigits word length right) (length + depth)
    (cylinderDigits_shared_prefix word length depth left right agreement)

/-- Both changes that occur between representatives are accounted for:
parameter movement and replacement of a complete tail with a shared prefix. -/
theorem cylinderCoordinate_derivative_displacement_bound {lower upper firstRatio secondRatio : ℝ}
    (lower_positive : 0 < lower) (upper_lt_one : upper < 1)
    (first_mem : firstRatio ∈ Set.Icc lower upper) (second_mem : secondRatio ∈ Set.Icc lower upper)
    (word : ℕ → Bool) (length depth : ℕ) (left right : ℕ → Bool)
    (agreement : ∀ index < depth, left index = right index) :
    |deriv (cylinderCoordinate word length left) firstRatio -
      deriv (cylinderCoordinate word length right) secondRatio| ≤
      ((length + depth : ℕ) : ℝ) * firstRatio ^ (length + depth - 1) +
        2 * addressParameterDerivativeBound upper * firstRatio ^ (length + depth) +
        addressParameterSecondDerivativeBound upper * |firstRatio - secondRatio| := by
  have tail_bound := cylinderCoordinate_shared_prefix_derivative_bound
    (lower_positive.trans_le first_mem.1) first_mem.2 upper_lt_one word length depth left right agreement
  have parameter_bound := address_parameter_derivative_lipschitz_estimate lower_positive upper_lt_one
    second_mem first_mem (cylinderDigits word length right)
  rw [← (hasDerivAt_cylinderCoordinate (lower_positive.trans_le first_mem.1)
      (first_mem.2.trans_lt upper_lt_one) word length right).deriv,
    ← (hasDerivAt_cylinderCoordinate (lower_positive.trans_le second_mem.1)
      (second_mem.2.trans_lt upper_lt_one) word length right).deriv] at parameter_bound
  exact (abs_sub_le (deriv (cylinderCoordinate word length left) firstRatio)
    (deriv (cylinderCoordinate word length right) firstRatio)
    (deriv (cylinderCoordinate word length right) secondRatio)).trans (add_le_add tail_bound parameter_bound)

end LambdaCantor.First.Roots
