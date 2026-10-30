import LambdaCantor.First.RationalNormalizationBounds
import LambdaCantor.First.TailDecay

noncomputable section
namespace LambdaCantor.First

/-- The differentiated geometric scale also vanishes. -/
theorem tendsto_nat_mul_pow_pred {upper : ℝ} (hpos : 0 < upper) (hlt : upper < 1) :
    Filter.Tendsto (fun length : ℕ => (length : ℝ) * upper ^ (length - 1))
      Filter.atTop (nhds (0 : ℝ)) := by
  have hmain := tendsto_scaled_address_derivative_majorant hpos hlt
  have htail := (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt).mul_const
    (addressParameterDerivativeBound upper)
  simpa only [add_sub_cancel_right, zero_mul, sub_zero] using hmain.sub htail

/-- Each exact binomial remainder term vanishes uniformly over every address.
The length and padding may grow independently. -/
theorem tendstoUniformly_powersFour_remainder_term {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : upper < 1) (hordered : lower ≤ upper)
    (depth padding : ℕ → ℕ) (hdepth : Filter.Tendsto depth Filter.atTop Filter.atTop)
    (power : ℕ) :
    TendstoUniformly
      (fun index (point : Set.Icc lower upper × (ℕ → Bool)) =>
        (point.1 : ℝ) ^ depth index *
          (-powersFourRightFactor (padding index) point.2 point.1) ^ power)
      (fun _ => (0 : ℝ)) Filter.atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  have hlimit := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (hlower.le.trans hordered) hupper).comp hdepth
  filter_upwards [hlimit.eventually (gt_mem_nhds hepsilon)] with index hindex
  intro point
  have hpos : 0 < (point.1 : ℝ) := hlower.trans_le point.1.property.1
  have hlt := point.1.property.2.trans_lt hupper
  have hunit := (powersFour_factors_mem_unit hpos.le hlt (padding index) point.2).2
  have habs : |-powersFourRightFactor (padding index) point.2 point.1| ≤ 1 := by
    simpa only [abs_neg, abs_of_nonneg hunit.1] using hunit.2
  simp only [dist_zero_left, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_nonneg (pow_nonneg hpos.le (depth index)), abs_of_nonneg hpos.le]
  apply lt_of_le_of_lt _ hindex
  calc
    _ ≤ (point.1 : ℝ) ^ depth index * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) habs) (by positivity)
    _ ≤ upper ^ depth index := by
      simpa only [mul_one] using pow_le_pow_left₀ hpos.le point.1.property.2 (depth index)

/-- Actual derivatives of every exact binomial remainder term vanish uniformly.
The estimate is uniform simultaneously in the parameter and the binary tail. -/
theorem tendstoUniformly_powersFour_remainder_term_derivative {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : upper < 1) (hordered : lower ≤ upper)
    (depth padding : ℕ → ℕ)
    (hdepth : Filter.Tendsto depth Filter.atTop Filter.atTop)
    (hpadding : Filter.Tendsto padding Filter.atTop Filter.atTop) (power : ℕ) :
    TendstoUniformly
      (fun index (point : Set.Icc lower upper × (ℕ → Bool)) =>
        deriv (fun parameter => parameter ^ depth index *
          (-powersFourRightFactor (padding index) point.2 parameter) ^ power) point.1)
      (fun _ => (0 : ℝ)) Filter.atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  have hupperPos := hlower.trans_le hordered
  have hfirst := (tendsto_nat_mul_pow_pred hupperPos hupper).comp hdepth
  have hsecond := ((tendsto_pow_atTop_nhds_zero_of_lt_one hupperPos.le hupper).comp hdepth).const_mul
    (power : ℝ)
  have hthird := (tendsto_scaled_address_derivative_majorant hupperPos hupper).comp hpadding
  have hlimit := hfirst.add (hsecond.mul hthird)
  simp only [mul_zero, zero_add] at hlimit
  filter_upwards [hlimit.eventually (gt_mem_nhds hepsilon)] with index hindex
  intro point
  have hpos : 0 < (point.1 : ℝ) := hlower.trans_le point.1.property.1
  have hlt := point.1.property.2.trans_lt hupper
  have hunit := (powersFour_factors_mem_unit hpos.le hlt (padding index) point.2).2
  have htailDerivative := (hasDerivAt_powersFourRightFactor hpos hlt (padding index) point.2).neg
  have habs : |-powersFourRightFactor (padding index) point.2 point.1| ≤ 1 := by
    simpa only [abs_neg, abs_of_nonneg hunit.1] using hunit.2
  have hderivative := powersFourRightFactor_derivative_bound hpos point.1.property.2
    hupper (padding index) point.2
  rw [(hasDerivAt_powersFourRightFactor hpos hlt (padding index) point.2).deriv] at hderivative
  have hnegativeDerivative : |-(-((padding index : ℝ) *
      (point.1 : ℝ) ^ (padding index - 1) * address point.1 point.2 +
        (point.1 : ℝ) ^ padding index * addressParameterDerivative point.1 point.2))| ≤
      (padding index : ℝ) * upper ^ (padding index - 1) +
        upper ^ padding index * addressParameterDerivativeBound upper := by
    simpa only [abs_neg] using hderivative
  simp only [dist_zero_left, Real.norm_eq_abs]
  exact (scaled_power_derivative_bound (depth index) power
    (fun parameter => -powersFourRightFactor (padding index) point.2 parameter)
    hpos.le point.1.property.2 htailDerivative habs hnegativeDerivative).trans_lt hindex

end LambdaCantor.First

