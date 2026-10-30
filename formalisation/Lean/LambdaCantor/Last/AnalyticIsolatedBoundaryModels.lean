import LambdaCantor.Last.AnalyticIsolatedHullRegions
import LambdaCantor.Last.AnalyticIsolatedMonotone

noncomputable section
namespace LambdaCantor.Last

theorem critical_weak_overlap_margins {ratio error : ℝ}
    (critical_equation : 2*ratio^2+2*ratio=1) (ratio_lower : (1/3 : ℝ) < ratio)
    (less_half : ratio < 1/2) (error_nonnegative : 0 ≤ error) (error_small : error ≤ 1/100) :
    (1-2*ratio)*(1+error) < ratio*(1+ratio-error) ∧
      (1-2*ratio)*(1+ratio+error) < 1-error := by
  constructor <;> nlinarith [mul_nonneg error_nonnegative (show 0 ≤ ratio by linarith)]

theorem boundary_linear_child_endpoints {ratio : ℝ}
    (critical_equation : 2*ratio^2+2*ratio=1) (digit : Bool × Bool) :
    positiveLinearContinuous (1+ratio) (wordMap ratio [digit] 0) = boundaryAffineLower ratio digit ∧
      positiveLinearContinuous (1+ratio) (wordMap ratio [digit] (1,1)) = boundaryAffineUpper ratio digit := by
  rcases digit with ⟨first, second⟩
  cases first <;> cases second <;> constructor <;>
    simp [positiveLinearContinuous, positiveLinear, wordMap, digitPoint,
      boundaryAffineLower, boundaryAffineUpper] <;> nlinarith

theorem ordered_of_approximate_pair {first second lower upper error : ℝ}
    (first_close : |first-lower| ≤ error) (second_close : |second-upper| ≤ error)
    (room : 2*error ≤ upper-lower) : first ≤ second := by
  have first_bounds := abs_le.mp first_close
  have second_bounds := abs_le.mp second_close
  linarith

theorem boundary_child_hulls_ordered {ratio error : ℝ}
    (ratio_lower : (1/3 : ℝ) < ratio) (less_half : ratio < 1/2) (error_small : error ≤ 1/100)
    (lower upper : Bool × Bool → ℝ)
    (lower_close : ∀ digit, |lower digit-boundaryAffineLower ratio digit| ≤ error)
    (upper_close : ∀ digit, |upper digit-boundaryAffineUpper ratio digit| ≤ error) :
    OrderedActualChildHulls lower upper := by
  constructor
  · apply ordered_of_approximate_pair (lower_close (false,false)) (lower_close (true,false))
    simp only [boundaryAffineLower]
    linarith
  · apply ordered_of_approximate_pair (lower_close (true,false)) (lower_close (false,true))
    simp only [boundaryAffineLower]
    linarith
  · apply ordered_of_approximate_pair (lower_close (false,true)) (lower_close (true,true))
    simp only [boundaryAffineLower]
    linarith
  · apply ordered_of_approximate_pair (upper_close (false,false)) (upper_close (true,false))
    simp only [boundaryAffineUpper]
    linarith
  · apply ordered_of_approximate_pair (upper_close (true,false)) (upper_close (false,true))
    simp only [boundaryAffineUpper]
    linarith
  · apply ordered_of_approximate_pair (upper_close (false,true)) (upper_close (true,true))
    simp only [boundaryAffineUpper]
    linarith

end LambdaCantor.Last
