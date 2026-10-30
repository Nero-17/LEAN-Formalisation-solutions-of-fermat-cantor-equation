import LambdaCantor.Last.AnalyticIrrationalLocalization
import LambdaCantor.Last.AnalyticLastPersistence
import LambdaCantor.Half

noncomputable section
namespace LambdaCantor.Last

/-- The new irrational route includes the critical parameter, and in fact a
slightly larger lower interval. It uses the full first slope band through
logarithmic endpoint sources, not the old non-strict irrational terminal. -/
theorem analytic_irrational_positive_dimension {exponent ratio : ℝ}
    (hirrational : Irrational exponent) (hexponent : 1 < exponent)
    (hlower : (183 / 500 : ℝ) ≤ ratio) (hhalf : ratio < 1 / 2) :
    0 < dimH (intersection exponent ratio) := by
  have hpositive : 0 < ratio := by linarith
  have hless : ratio < 1 := by linarith
  obtain ⟨difference, first, hfirst_outer, second, hsecond_outer, hslower, hsupper⟩ :=
    exists_trimmed_logarithmic_center hlower hhalf hexponent
  have hfirst_bounds := outerCantor_bounds hpositive.le hless hfirst_outer
  have hsecond_bounds := outerCantor_bounds hpositive.le hless hsecond_outer
  have hfirst_positive : 0 < first := by linarith [hfirst_bounds.1]
  have hsecond_positive : 0 < second := by linarith [hsecond_bounds.1]
  have hfirst_mem := outerCantor_subset_cantorSet hpositive.le hless hfirst_outer
  have hsecond_mem := outerCantor_subset_cantorSet hpositive.le hless hsecond_outer
  obtain ⟨firstWord, secondWord, coefficient, hcoefficient, hfirst, hsecond, hlower_corner, hupper_corner, bands⟩ :=
    localize_logarithmic_center hexponent hpositive hhalf hfirst_positive hsecond_positive
      hfirst_mem hsecond_mem difference (rational_trimmed_first_band hlower hhalf hslower hsupper)
  obtain ⟨firstDepth, secondDepth, hscale_limit, hcoefficient_limit⟩ :=
    irrational_actual_source_sequences hirrational (show 0 < exponent by linarith)
      hpositive hless hcoefficient
  exact logarithmic_endpoint_transfer_sequences hexponent hpositive hhalf hcoefficient
    firstWord secondWord hfirst hsecond hlower_corner hupper_corner bands
    firstDepth secondDepth hscale_limit hcoefficient_limit

theorem analytic_irrational_last_upper {exponent : ℝ}
    (hirrational : Irrational exponent) (hexponent : 1 < exponent) :
    lastTransition exponent ≤ 183 / 500 := by
  apply lastTransition_le_of_nonnegative_bound (by norm_num)
  intro ratio hratio hlower
  rcases lt_or_eq_of_le hratio.2 with hhalf | hhalf
  · exact analytic_irrational_positive_dimension hirrational hexponent hlower.le hhalf
  · rw [hhalf]
    exact positive_dimH_intersection_half (by linarith)

theorem analytic_irrational_last_strict_upper {exponent : ℝ}
    (hirrational : Irrational exponent) (hexponent : 1 < exponent) :
    lastTransition exponent < (Real.sqrt 3 - 1) / 2 := by
  apply (analytic_irrational_last_upper hirrational hexponent).trans_lt
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hnonnegative := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

end LambdaCantor.Last
