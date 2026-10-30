import LambdaCantor.AE.CenteredSecondDecay

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.AE

/-- Actual irrational depth choices make the centered Taylor remainder
and its first two parameter derivatives vanish. The conclusion permits
arbitrary parameter and address sequences, expressing uniform control
on the fixed compact band without a rate assumption on irrationality. -/
theorem centered_actual_C2_depth_sequences {exponent center lower upper : ℝ}
    (hirrational : Irrational exponent) (hexponent : 1 < exponent)
    (hcenter : 0 < center) (hcenterLess : center < 1)
    (hlower : 0 < lower) (hinterval : lower ≤ upper) (hless : upper < 1) :
    ∃ horizontalDepth verticalDepth : ℕ → ℕ,
      (∀ index, index ≤ horizontalDepth index ∧ index ≤ verticalDepth index ∧ 2 ≤ verticalDepth index) ∧
      (∀ index,
        |(verticalDepth index : ℝ) - exponent * horizontalDepth index +
          Real.log exponent / Real.log center| < (center ^ index) ^ 2 ∧
        (verticalDepth index : ℝ) ^ 2 * upper ^ verticalDepth index < (center ^ index) ^ 3) ∧
      ∀ ratios : ℕ → ℝ, (∀ index, ratios index ∈ Set.Icc lower upper) →
      ∀ digits : ℕ → ℕ → Bool,
        Tendsto (fun index => centeredRemainderFunction exponent (horizontalDepth index)
          (verticalDepth index) index (digits index) (ratios index)) atTop (𝓝 0) ∧
        Tendsto (fun index => centeredRemainderFirst exponent (horizontalDepth index)
          (verticalDepth index) index (digits index) (ratios index)) atTop (𝓝 0) ∧
        Tendsto (fun index => centeredRemainderSecond exponent (horizontalDepth index)
          (verticalDepth index) index (digits index) (ratios index)) atTop (𝓝 0) := by
  obtain ⟨horizontalDepth, verticalDepth, hdepth, hchoice, henvelope⟩ :=
    centered_normalized_depth_sequences hirrational hexponent hcenter hcenterLess hlower hinterval hless
  obtain ⟨secondBound, hsecondPositive, hsecondUniform⟩ :=
    centered_address_uniform_second_bound (hlower.trans_le hinterval) hless
  refine ⟨horizontalDepth, verticalDepth, hdepth, hchoice, ?_⟩
  intro ratios hratios digits
  have hphase : ∀ index, |(verticalDepth index : ℝ) - exponent * horizontalDepth index -
      (-Real.log exponent / Real.log center)| ≤ 1 := by
    intro index
    have hscale : (center ^ index) ^ 2 ≤ 1 :=
      pow_le_one₀ (pow_nonneg hcenter.le _) (pow_le_one₀ hcenter.le hcenterLess.le)
    simpa only [neg_div, sub_neg_eq_add] using ((hchoice index).1.le.trans hscale)
  have hfirst : ∀ index,
      |deriv (fun parameter => address parameter (digits index)) (ratios index)| ≤
        addressParameterDerivativeBound upper := by
    intro index
    rw [(hasDerivAt_address_parameter (hlower.trans_le (hratios index).1)
      ((hratios index).2.trans_lt hless) (digits index)).deriv]
    exact address_parameter_derivative_bound (hlower.le.trans (hratios index).1)
      (hratios index).2 hless (digits index)
  have hsecond : ∀ index,
      |deriv (deriv (fun parameter => address parameter (digits index))) (ratios index)| ≤ secondBound := by
    intro index
    exact hsecondUniform (digits index) (ratios index)
      ⟨hlower.trans_le (hratios index).1, (hratios index).2⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa only [centeredRemainderFunction] using centered_actual_remainder_tendsto_zero
      hexponent hlower hinterval hless horizontalDepth verticalDepth
      (fun index => (hdepth index).2.1) (fun index => (hdepth index).2.2)
      ratios hratios digits (henvelope ratios hratios)
  · exact centeredRemainderFirst_tendsto_zero hexponent hlower hinterval hless
      horizontalDepth verticalDepth (fun index => (hdepth index).2.1)
      (fun index => (hdepth index).2.2) hphase ratios hratios digits hfirst (henvelope ratios hratios)
  · exact centeredRemainderSecond_tendsto_zero hexponent hlower hinterval hless
      horizontalDepth verticalDepth (fun index => (hdepth index).2.1)
      (fun index => (hdepth index).2.2) hphase ratios hratios digits hfirst hsecond (henvelope ratios hratios)

end LambdaCantor.AE
