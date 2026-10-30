import LambdaCantor.Integer.NearAxisStrictDifferentiable
import LambdaCantor.Integer.NearAxisNormalizedTangent
import LambdaCantor.Integer.NearAxisDimension
import LambdaCantor.Integer.GoodSlopePositiveDimension

namespace LambdaCantor.Integer

/-- Strict finite logarithmic corners in a direct good band imply positive
Hausdorff dimension of the actual Fermat intersection. -/
theorem strict_log_source_positive_dimension (n d p q P Q : ℕ) (a b : ℝ)
    (exponent : 3 ≤ n) (positiveP : 0 < P) (positiveQ : 0 < Q)
    (prefixP : ternaryPrefix P p = true) (prefixQ : ternaryPrefix Q q = true)
    (boundQ : Q+1 ≤ 3^q)
    (lowerBand : 1 < a) (upperBand : b < 3) (positiveB : 0 < b)
    (bandGood : ∀ slope : ℝ, a < slope → slope < b → GoodSlope slope)
    (lowerRatio : a/Q < (n : ℝ)/(P+1))
    (upperRatio : (n : ℝ)/P < b/(Q+1))
    (lowerCorner : nearAxisLog n d p q P Q 0 0 0 < 0)
    (upperCorner : 0 < nearAxisLog n d p q P Q 0 1 1) :
    0 < dimH (intersection (n : ℝ) (1/3)) := by
  obtain ⟨k,_,_,nonisolated,uncountable,small,residual,slopes⟩ := near_axis_perfect_source
    n d p q P Q a b exponent positiveP positiveQ boundQ lowerBand upperBand positiveB bandGood
      lowerRatio upperRatio lowerCorner upperCorner
  obtain ⟨point,member,irrational⟩ := exists_irrational_tangent _ uncountable _
    (near_axis_normalized_tangent_injective n d p q k P Q exponent positiveP positiveQ boundQ small residual)
  have firstCantor : point.1 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]; exact member.1.1
  have secondCantor : point.2 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]; exact member.1.2
  have firstBounds := _root_.cantorSet_subset_unitInterval firstCantor
  have secondBounds := _root_.cantorSet_subset_unitInterval secondCantor
  have slopeFacts := slopes _ firstBounds _ secondBounds
  have positivePReal : (0 : ℝ) < P := by exact_mod_cast positiveP
  obtain ⟨derivative,strict,formula⟩ := nearAxisLog_hasStrictFDerivAt
    n d p q P Q ((1/3 : ℝ)^(n*k+d)) point.1 point.2
      (by linarith [firstBounds.1]) (residual _ secondBounds)
  have dimension := good_slope_positive_dimension_of_derivative
    (fun value : ℝ × ℝ => nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d)) value.1 value.2)
    0 _ _ slopeFacts.1 slopeFacts.2 irrational ⟨point,member⟩
    (nonisolated ⟨point,member⟩) derivative strict formula
  exact dimension.trans_le (near_axis_dimension_le_intersection n d p q k P Q positiveP positiveQ
    boundQ prefixP prefixQ small residual)

end LambdaCantor.Integer
