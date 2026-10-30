import LambdaCantor.RealPowers.IrrationalSource
import LambdaCantor.RealPowers.DeepSource
import LambdaCantor.RealPowers.EndpointWords

noncomputable section
namespace LambdaCantor.RealPowers
open Integer Last

/-- The deep source conditions are constructed from two finite endpoints and
an integral cylinder-depth difference. This closes the coefficient and small
horizontal-error obligations in the direct orientation. -/
theorem irrational_positive_from_direct_endpoint_pair {exponent : ℝ}
    (exponent_gt_one : 1 < exponent) (exponent_irrational : Irrational exponent)
    (firstWord secondWord : List Bool) (same_length : firstWord.length = secondWord.length)
    (first_positive : 0 < scalarWordMap (1/3) firstWord 0)
    (second_positive : 0 < scalarWordMap (1/3) secondWord 0)
    (shift : ℕ)
    (good : GoodSlope (exponent*(1/3 : ℝ)^shift*
      scalarWordMap (1/3) secondWord 0/scalarWordMap (1/3) firstWord 0))
    (slope_irrational : ∀ rational : ℚ, exponent*(1/3 : ℝ)^shift*
      scalarWordMap (1/3) secondWord 0/scalarWordMap (1/3) firstWord 0 ≠ (rational : ℝ)) :
    0 < dimH (intersection exponent (1/3)) := by
  obtain ⟨epsilon, epsilon_positive, source_criterion⟩ := irrational_finite_source_criterion
    exponent_gt_one exponent_irrational _ good slope_irrational
  have slope_bounds := goodSlope_between_one_three good
  have level_member : (1/3 : ℝ) ∈ switchSet
      (exponent*(1/3 : ℝ)^shift*scalarWordMap (1/3) secondWord 0/
        scalarWordMap (1/3) firstWord 0) := by
    exact Or.inl (Or.inl ⟨le_rfl, by linarith [slope_bounds.1]⟩)
  obtain ⟨delta, delta_positive, deep_source⟩ := deep_source_horizontal_error exponent
    (scalarWordMap (1/3) firstWord 0) (scalarWordMap (1/3) secondWord 0)
    ((1/3 : ℝ)^shift) (1/3) first_positive second_positive epsilon epsilon_positive
  obtain ⟨depth, scale_small⟩ := exists_pow_lt_of_lt_one delta_positive (by norm_num : (1/3 : ℝ) < 1)
  have horizontal_positive : 0 < (1/3 : ℝ)^(firstWord.length+(shift+depth)) := by positivity
  have vertical_positive : 0 < (1/3 : ℝ)^(secondWord.length+depth) := by positivity
  have horizontal_small : (1/3 : ℝ)^(firstWord.length+(shift+depth)) < delta :=
    (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/3) (by norm_num)
      (by omega : depth ≤ firstWord.length+(shift+depth))).trans_lt scale_small
  have vertical_small : (1/3 : ℝ)^(secondWord.length+depth) < delta :=
    (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/3) (by norm_num)
      (by omega : depth ≤ secondWord.length+depth)).trans_lt scale_small
  have scale_ratio : (1/3 : ℝ)^(firstWord.length+(shift+depth))/
      (1/3 : ℝ)^(secondWord.length+depth) = (1/3 : ℝ)^shift := by
    apply (div_eq_iff vertical_positive.ne').mpr
    rw [← pow_add]
    congr 1
    omega
  obtain ⟨coefficient_positive, source_level, horizontal_error⟩ := deep_source
    ((1/3 : ℝ)^(firstWord.length+(shift+depth))) ((1/3 : ℝ)^(secondWord.length+depth))
    horizontal_positive vertical_positive horizontal_small vertical_small scale_ratio
  apply source_criterion
    ((scalarWordMap (1/3) firstWord 0)^exponent/
      (scalarWordMap (1/3) secondWord 0+(1/3 : ℝ)^(secondWord.length+depth)*(1-2*(1/3))))
    coefficient_positive (firstWord++List.replicate (shift+depth) false)
      (secondWord++List.replicate depth false)
  · intro coordinate coordinate_bounds
    simpa only [List.length_append, List.length_replicate, append_zeros_left_endpoint] using
      (horizontal_error coordinate coordinate_bounds).le
  · rw [scalarWordMap_affine (1/3) (secondWord++List.replicate depth false) 1]
    simpa only [List.length_append, List.length_replicate, append_zeros_left_endpoint, mul_one,
      source_level] using level_member

end LambdaCantor.RealPowers

