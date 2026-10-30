import LambdaCantor.First.RealNormalizationBounds
import LambdaCantor.First.PhaseContinuity
import LambdaCantor.First.LeadingRealTails

noncomputable section
namespace LambdaCantor

/-- The exact divided-remainder error vanishes in C1, uniformly in every
parameter and every complete right address. -/
theorem tendstoUniformly_realNormalizationError (exponent : ℝ) {lower upper phase : ℝ}
    (hlower : 0 < lower) (hupper : upper < 1) (hordered : lower ≤ upper) (hphase : 0 < phase)
    {phases : ℕ → ℝ} (hphases : Filter.Tendsto phases Filter.atTop (nhds phase))
    {depth padding : ℕ → ℕ} (hdepth : Filter.Tendsto depth Filter.atTop Filter.atTop)
    (hpadding : Filter.Tendsto padding Filter.atTop Filter.atTop) :
    TendstoUniformly
      (fun index (point : Set.Icc lower upper × (ℕ → Bool)) =>
        realNormalizationError exponent (phases index) (depth index) (padding index) point.2 point.1)
      (fun _ => (0 : ℝ)) Filter.atTop ∧
    TendstoUniformly
      (fun index (point : Set.Icc lower upper × (ℕ → Bool)) =>
        deriv (realNormalizationError exponent (phases index) (depth index) (padding index) point.2) point.1)
      (fun _ => (0 : ℝ)) Filter.atTop := by
  obtain ⟨valueBound, derivativeBound, hvalue, hderivative, hbound⟩ := realNormalizationError_bounds exponent
  have hupperpos := lt_of_lt_of_le hlower hordered
  have hpower := tendsto_pow_atTop_nhds_zero_of_lt_one hupperpos.le hupper
  have hdepthPower := hpower.comp hdepth
  have hpaddingDerivative := (tendsto_scaled_address_derivative_majorant hupperpos hupper).comp hpadding
  have hweighted : Filter.Tendsto (fun index : ℕ =>
      (index : ℝ) * upper ^ (index - 1)) Filter.atTop (nhds (0 : ℝ)) := by
    have h := (tendsto_scaled_address_derivative_majorant hupperpos hupper).sub
      (hpower.mul_const (addressParameterDerivativeBound upper))
    convert h using 1
    · funext index
      ring
    · simp
  have hvalueLimit := hdepthPower.const_mul valueBound
  have hderivativeLimit := (hdepthPower.const_mul ((phase + 1) / lower + 1) |>.const_mul valueBound).add
    (((hweighted.comp hdepth).add hdepthPower).const_mul derivativeBound)
  have heventual : ∀ᶠ index in Filter.atTop,
      0 ≤ phases index ∧ phases index ≤ phase + 1 ∧ 1 ≤ padding index ∧
      upper ^ depth index ≤ (1 / 2 : ℝ) ∧
      (padding index : ℝ) * upper ^ (padding index - 1) +
        upper ^ padding index * addressParameterDerivativeBound upper ≤ 1 := by
    filter_upwards [hphases.eventually (lt_mem_nhds hphase),
      hphases.eventually (gt_mem_nhds (show phase < phase + 1 by linarith)),
      hpadding.eventually (Filter.eventually_ge_atTop 1),
      hdepthPower.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
      hpaddingDerivative.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with index hnonnegative hbounded hpad hsmall hpadD
    exact ⟨hnonnegative.le, hbounded.le, hpad, hsmall.le, hpadD.le⟩
  constructor
  · apply Metric.tendstoUniformly_iff.mpr
    intro epsilon hepsilon
    filter_upwards [heventual, hvalueLimit.eventually
      (gt_mem_nhds (by simpa using hepsilon))] with index hi hsmall
    intro point
    simp only [dist_zero_left, Real.norm_eq_abs]
    exact lt_of_le_of_lt ((hbound lower upper point.1 (phases index) (phase + 1)
      (depth index) (padding index) point.2 hlower point.1.property.1 point.1.property.2
      hupper hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2).1) hsmall
  · apply Metric.tendstoUniformly_iff.mpr
    intro epsilon hepsilon
    filter_upwards [heventual, hderivativeLimit.eventually
      (gt_mem_nhds (by simpa using hepsilon))] with index hi hsmall
    intro point
    simp only [dist_zero_left, Real.norm_eq_abs]
    apply lt_of_le_of_lt ((hbound lower upper point.1 (phases index) (phase + 1)
      (depth index) (padding index) point.2 hlower point.1.property.1 point.1.property.2
      hupper hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2).2)
    convert hsmall using 1 <;> simp only [Function.comp_apply] <;> ring




theorem tendstoUniformly_real_phase_tail {lower upper phase : ℝ}
    (hlower : 0 < lower) (hupper : upper < 1) (hordered : lower ≤ upper) (hphase : 0 < phase)
    {phases : ℕ → ℝ} (hphases : Filter.Tendsto phases Filter.atTop (nhds phase))
    {padding : ℕ → ℕ} (hpadding : Filter.Tendsto padding Filter.atTop Filter.atTop) :
    TendstoUniformly
      (fun index (point : Set.Icc lower upper × (ℕ → Bool)) =>
        (point.1 : ℝ) ^ phases index * ((point.1 : ℝ) ^ padding index * address point.1 point.2))
      (fun _ => (0 : ℝ)) Filter.atTop ∧
    TendstoUniformly
      (fun index (point : Set.Icc lower upper × (ℕ → Bool)) =>
        deriv (fun parameter : ℝ => parameter ^ phases index *
          (parameter ^ padding index * address parameter point.2)) point.1)
      (fun _ => (0 : ℝ)) Filter.atTop := by
  have hupperpos := lt_of_lt_of_le hlower hordered
  have hpower := (tendsto_pow_atTop_nhds_zero_of_lt_one hupperpos.le hupper).comp hpadding
  have hmajorant := (tendsto_scaled_address_derivative_majorant hupperpos hupper).comp hpadding
  have hderivative := (hpower.const_mul ((phase + 1) / lower)).add hmajorant
  have heventual : ∀ᶠ index in Filter.atTop, 0 ≤ phases index ∧ phases index ≤ phase + 1 := by
    filter_upwards [hphases.eventually (lt_mem_nhds hphase),
      hphases.eventually (gt_mem_nhds (show phase < phase + 1 by linarith))] with index hi hj
    exact ⟨hi.le, hj.le⟩
  constructor
  · apply Metric.tendstoUniformly_iff.mpr
    intro epsilon hepsilon
    filter_upwards [heventual, hpower.eventually (gt_mem_nhds hepsilon)] with index hi hsmall
    intro point
    simp only [dist_zero_left, Real.norm_eq_abs]
    exact ((real_phase_tail_bounds hlower point.1.property.1 point.1.property.2 hupper
      hi.1 hi.2 (padding index) point.2).1).trans_lt hsmall
  · apply Metric.tendstoUniformly_iff.mpr
    intro epsilon hepsilon
    filter_upwards [heventual, hderivative.eventually
      (gt_mem_nhds (by simpa using hepsilon))] with index hi hsmall
    intro point
    simp only [dist_zero_left, Real.norm_eq_abs]
    exact ((real_phase_tail_bounds hlower point.1.property.1 point.1.property.2 hupper
      hi.1 hi.2 (padding index) point.2).2).trans_lt hsmall

end LambdaCantor
