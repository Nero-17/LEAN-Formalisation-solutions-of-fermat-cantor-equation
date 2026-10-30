import LambdaCantor.RealPowers.ActualSourceCriterion
import LambdaCantor.RealPowers.StrictSource
import LambdaCantor.RealPowers.DeepSource
import LambdaCantor.RealPowers.EndpointWords

noncomputable section
namespace LambdaCantor.RealPowers
open Integer Last

/-- Reciprocal source orientation: divide the actual source by its limiting
horizontal derivative and use the coordinate-swapped strict-return criterion.
The half-normalized level is adjusted before choosing the coefficient. -/
theorem irrational_positive_from_reciprocal_endpoint_pair {exponent : ℝ}
    (exponent_gt_one : 1 < exponent) (exponent_irrational : Irrational exponent)
    (firstWord secondWord : List Bool) (same_length : firstWord.length = secondWord.length)
    (first_positive : 0 < scalarWordMap (1/3) firstWord 0)
    (second_positive : 0 < scalarWordMap (1/3) secondWord 0)
    (shift : ℕ)
    (good : GoodSlope (1/(exponent*(1/3 : ℝ)^shift*
      scalarWordMap (1/3) secondWord 0/scalarWordMap (1/3) firstWord 0)))
    (slope_irrational : ∀ rational : ℚ, 1/(exponent*(1/3 : ℝ)^shift*
      scalarWordMap (1/3) secondWord 0/scalarWordMap (1/3) firstWord 0) ≠ (rational : ℝ)) :
    0 < dimH (intersection exponent (1/3)) := by
  let slope := exponent*(1/3 : ℝ)^shift*scalarWordMap (1/3) secondWord 0/
    scalarWordMap (1/3) firstWord 0
  have slope_positive : 0 < slope := by dsimp [slope]; positivity
  obtain ⟨epsilon, epsilon_positive, neighborhood, neighborhood_open,
    contained, criterion⟩ := good_slope_uniform_source_swapped (1/slope) good slope_irrational
  have slope_bounds : 1 < 1/slope ∧ 1/slope < 3 := goodSlope_between_one_three good
  have level_member : (1/3 : ℝ) ∈ switchSet (1/slope) := by
    exact Or.inl (Or.inl ⟨le_rfl, by linarith [slope_bounds.1]⟩)
  obtain ⟨delta, delta_positive, deep_source⟩ := deep_source_horizontal_error exponent
    (scalarWordMap (1/3) firstWord 0) (scalarWordMap (1/3) secondWord 0)
    ((1/3 : ℝ)^shift) (slope*(1/3)) first_positive second_positive
    (slope*epsilon) (mul_pos slope_positive epsilon_positive)
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
  have vertical_center : 1/(2*slope) = (1/slope)/2 := by
    field_simp [slope_positive.ne']
  apply actual_irrational_source_with_normalization exponent_gt_one exponent_irrational slope slope_positive
    (1/2) epsilon epsilon_positive neighborhood neighborhood_open
    (by simpa only [vertical_center] using criterion)
    ((scalarWordMap (1/3) firstWord 0)^exponent/
      (scalarWordMap (1/3) secondWord 0+(1/3 : ℝ)^(secondWord.length+depth)*(1-2*(slope*(1/3)))))
    coefficient_positive (firstWord++List.replicate (shift+depth) false)
      (secondWord++List.replicate depth false)
  · intro coordinate coordinate_bounds
    simp only [List.length_append, List.length_replicate, append_zeros_left_endpoint]
    have estimate := horizontal_error coordinate coordinate_bounds
    change |(exponent*(1/3 : ℝ)^(firstWord.length+(shift+depth))*
      (scalarWordMap (1/3) firstWord 0+
        (1/3 : ℝ)^(firstWord.length+(shift+depth))*coordinate)^(exponent-1))/
      (2*((scalarWordMap (1/3) firstWord 0)^exponent/
        (scalarWordMap (1/3) secondWord 0+(1/3 : ℝ)^(secondWord.length+depth)*(1-2*(slope*(1/3)))))*
        (1/3 : ℝ)^(secondWord.length+depth))-slope/2| < slope*epsilon at estimate
    have divided : |(exponent*(1/3 : ℝ)^(firstWord.length+(shift+depth))*
      (scalarWordMap (1/3) firstWord 0+
        (1/3 : ℝ)^(firstWord.length+(shift+depth))*coordinate)^(exponent-1))/
      (2*((scalarWordMap (1/3) firstWord 0)^exponent/
        (scalarWordMap (1/3) secondWord 0+(1/3 : ℝ)^(secondWord.length+depth)*(1-2*(slope*(1/3)))))*
        (1/3 : ℝ)^(secondWord.length+depth))-slope/2|/slope < epsilon :=
      (div_lt_iff₀ slope_positive).mpr (by nlinarith [estimate])
    have identity : ∀ value : ℝ, value/slope-1/2 = (value-slope/2)/slope := by
      intro value
      field_simp [slope_positive.ne']
      <;> ring
    rw [show ∀ value denominator : ℝ, value/(denominator*slope) = (value/denominator)/slope by
      intro value denominator; exact (div_div value denominator slope).symm]
    rw [identity, abs_div, abs_of_pos slope_positive]
    exact divided.le
  · rw [scalarWordMap_affine (1/3) (secondWord++List.replicate depth false) 1]
    simp only [List.length_append, List.length_replicate, append_zeros_left_endpoint, mul_one]
    have divided_level := congrArg (fun value : ℝ => value/slope) source_level
    rw [div_div] at divided_level
    have level_identity : (slope*(1/3))/slope = (1/3 : ℝ) := by
      field_simp [slope_positive.ne']
    rw [level_identity] at divided_level
    rw [divided_level]
    exact contained level_member

end LambdaCantor.RealPowers

