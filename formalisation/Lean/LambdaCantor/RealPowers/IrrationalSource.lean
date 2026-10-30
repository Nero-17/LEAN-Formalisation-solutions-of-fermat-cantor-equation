import LambdaCantor.RealPowers.StrictSource
import LambdaCantor.RealPowers.NormalizedPartials
import LambdaCantor.Last.IrrationalRescaling
import LambdaCantor.RealPowers.ActualCylinderEmbedding
import LambdaCantor.RealPowers.NormalizedLimits
import LambdaCantor.Last.UniformCoefficient
import LambdaCantor.RealPowers.SourceTransformations

noncomputable section
open Filter
open scoped NNReal Topology
namespace LambdaCantor.RealPowers
open Integer Last

/-- Finite-source criterion for an actual irrational-exponent intersection.
The hypotheses concern only a fixed positive Cantor rectangle and its limiting
source. Irrational rotation, uniform vertical control, actual integer depths,
strict-return persistence and the Hausdorff-dimension transfer are all proved
inside the theorem. Finding such finite source data for every exponent is a
separate source-selection theorem. -/
theorem irrational_finite_source_criterion {exponent : ℝ}
    (exponent_gt_one : 1 < exponent) (exponent_irrational : Irrational exponent)
    (slope : ℝ) (good : GoodSlope slope)
    (slope_irrational : ∀ rational : ℚ, slope ≠ (rational : ℝ)) :
    ∃ epsilon > 0, ∀ coefficient : ℝ, 0 < coefficient →
      ∀ firstWord secondWord : List Bool,
      (∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
        |(exponent*(1/3 : ℝ)^firstWord.length*
          (scalarWordMap (1/3) firstWord 0+
            (1/3 : ℝ)^firstWord.length*coordinate)^(exponent-1))/
              (2*coefficient*(1/3 : ℝ)^secondWord.length)-slope/2| ≤ epsilon) →
      -((scalarWordMap (1/3) firstWord 0)^exponent-
          coefficient*scalarWordMap (1/3) secondWord 1)/
        (2*coefficient*(1/3 : ℝ)^secondWord.length) ∈ switchSet slope →
      0 < dimH (intersection exponent (1/3)) := by
  obtain ⟨epsilon, epsilon_positive, neighborhood, neighborhood_open,
    contained, source_criterion⟩ := good_slope_uniform_source slope good slope_irrational
  refine ⟨epsilon, epsilon_positive, ?_⟩
  intro coefficient coefficient_positive firstWord secondWord horizontal_close source_level
  have exponent_positive : 0 < exponent := by linarith
  have height_positive : 0 < 2*coefficient*(1/3 : ℝ)^secondWord.length := by positivity
  have secondScale_positive : 0 < (1/3 : ℝ)^secondWord.length := by positivity
  obtain ⟨firstDepth, secondDepth, scale_limit, coefficient_limit⟩ :=
    irrational_actual_source_sequences exponent_irrational exponent_positive
      (by norm_num : (0 : ℝ) < 1/3) (by norm_num) coefficient_positive
  have vertical_eventual := coefficient_power_factor_eventually_uniform
    (exponent := exponent) (epsilon := 2*coefficient*epsilon)
    (fun index => (pow_pos (by norm_num : (0 : ℝ) < 1/3) (secondDepth index)).le)
    scale_limit coefficient_limit
    (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) coefficient_positive) epsilon_positive)
  have corner_limit := (normalizedCylinderSource_limit exponent_positive.ne'
    (fun index => pow_pos (by norm_num : (0 : ℝ) < 1/3) (secondDepth index))
    scale_limit coefficient_limit
    (scalarWordMap (1/3) firstWord 0) ((1/3 : ℝ)^firstWord.length)
    (scalarWordMap (1/3) secondWord 1) ((1/3 : ℝ)^secondWord.length) (0,0)).neg.div_const
      (2*coefficient*(1/3 : ℝ)^secondWord.length)
  simp only [mul_zero, add_zero, sub_zero] at corner_limit
  have corner_eventual := corner_limit.eventually
    (neighborhood_open.mem_nhds (contained source_level))
  obtain ⟨index, vertical_close, corner_inside⟩ := (vertical_eventual.and corner_eventual).exists
  apply positive_dimension_of_nearAxisCylinderSource
    (by norm_num : (0 : ℝ) < 1/3) (by norm_num) exponent_positive
    (firstDepth index) (secondDepth index) firstWord secondWord
  apply positive_dimension_of_source_div height_positive.ne'
  apply source_criterion
    (fun x y => normalizedCylinderSource exponent
      (exponent*(1/3 : ℝ)^(secondDepth index)/((1/3 : ℝ)^(firstDepth index))^exponent)
      ((1/3 : ℝ)^(secondDepth index))
      (scalarWordMap (1/3) firstWord 0) ((1/3 : ℝ)^firstWord.length)
      (scalarWordMap (1/3) secondWord 1) ((1/3 : ℝ)^secondWord.length) (x,y)/
        (2*coefficient*(1/3 : ℝ)^secondWord.length)) 0
  · apply Classical.coordinateBounds_of_hasDerivAt
      (fun x y => normalizedCylinderSource exponent
        (exponent*(1/3 : ℝ)^(secondDepth index)/((1/3 : ℝ)^(firstDepth index))^exponent)
        ((1/3 : ℝ)^(secondDepth index))
        (scalarWordMap (1/3) firstWord 0) ((1/3 : ℝ)^firstWord.length)
        (scalarWordMap (1/3) secondWord 1) ((1/3 : ℝ)^secondWord.length) (x,y)/
          (2*coefficient*(1/3 : ℝ)^secondWord.length))
      (fun x _ => (exponent*(1/3 : ℝ)^firstWord.length*
        (scalarWordMap (1/3) firstWord 0+(1/3 : ℝ)^firstWord.length*x)^(exponent-1))/
          (2*coefficient*(1/3 : ℝ)^secondWord.length))
      (fun _ y => ((exponent*(1/3 : ℝ)^(secondDepth index)/
          ((1/3 : ℝ)^(firstDepth index))^exponent)*(1/3 : ℝ)^secondWord.length*
          (1-(1/3 : ℝ)^(secondDepth index)*scalarWordMap (1/3) secondWord 1+
            (1/3 : ℝ)^(secondDepth index)*(1/3 : ℝ)^secondWord.length*y)^(exponent-1))/
          (2*coefficient*(1/3 : ℝ)^secondWord.length))
    · intro x hx y hy
      exact normalized_source_horizontal_derivative exponent_gt_one.le _ _ _ _ _ _ _ x y
    · intro x hx y hy
      exact normalized_source_vertical_derivative exponent_gt_one.le (by positivity) _ _ _ _ _ _ x y
    · intro x hx y hy
      have estimate := abs_le.mp (horizontal_close x hx)
      constructor <;> linarith [estimate.1, estimate.2]
    · intro x hx y hy
      have reflected_bounds : 1-y ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> linarith [hy.1, hy.2]
      have cylinder_bounds := scalarWordMap_bounds (by norm_num : (0 : ℝ) ≤ 1/3)
        (by norm_num) secondWord reflected_bounds
      have estimate := vertical_close (scalarWordMap (1/3) secondWord (1-y)) cylinder_bounds
      have base_identity :
          1-(1/3 : ℝ)^(secondDepth index)*scalarWordMap (1/3) secondWord 1+
            (1/3 : ℝ)^(secondDepth index)*(1/3 : ℝ)^secondWord.length*y =
          1-(1/3 : ℝ)^(secondDepth index)*scalarWordMap (1/3) secondWord (1-y) := by
        rw [scalarWordMap_affine (1/3) secondWord 1,
          scalarWordMap_affine (1/3) secondWord (1-y)]
        ring
      rw [base_identity]
      have normalized_error :
          ((exponent*(1/3 : ℝ)^(secondDepth index)/((1/3 : ℝ)^(firstDepth index))^exponent)*
              (1/3 : ℝ)^secondWord.length*
              (1-(1/3 : ℝ)^(secondDepth index)*scalarWordMap (1/3) secondWord (1-y))^(exponent-1))/
            (2*coefficient*(1/3 : ℝ)^secondWord.length)-1/2 =
          (((exponent*(1/3 : ℝ)^(secondDepth index)/((1/3 : ℝ)^(firstDepth index))^exponent)*
              (1-(1/3 : ℝ)^(secondDepth index)*scalarWordMap (1/3) secondWord (1-y))^(exponent-1))-
            coefficient)/(2*coefficient) := by
        field_simp [coefficient_positive.ne', secondScale_positive.ne']
        <;> ring
      have error_bound : |((exponent*(1/3 : ℝ)^(secondDepth index)/
            ((1/3 : ℝ)^(firstDepth index))^exponent)*(1/3 : ℝ)^secondWord.length*
            (1-(1/3 : ℝ)^(secondDepth index)*scalarWordMap (1/3) secondWord (1-y))^(exponent-1))/
          (2*coefficient*(1/3 : ℝ)^secondWord.length)-1/2| < epsilon := by
        rw [normalized_error, abs_div, abs_of_pos (by positivity : 0 < 2*coefficient)]
        exact (div_lt_iff₀ (by positivity : 0 < 2*coefficient)).mpr (by simpa [mul_assoc, mul_comm, mul_left_comm] using estimate)
      have error_sides := abs_lt.mp error_bound
      constructor <;> linarith [error_sides.1, error_sides.2]
  · change neighborhood (0-normalizedCylinderSource exponent
      (exponent*(1/3 : ℝ)^(secondDepth index)/((1/3 : ℝ)^(firstDepth index))^exponent)
      ((1/3 : ℝ)^(secondDepth index))
      (scalarWordMap (1/3) firstWord 0) ((1/3 : ℝ)^firstWord.length)
      (scalarWordMap (1/3) secondWord 1) ((1/3 : ℝ)^secondWord.length) (0,0)/
        (2*coefficient*(1/3 : ℝ)^secondWord.length))
    simpa only [zero_sub, neg_div] using corner_inside

end LambdaCantor.RealPowers

