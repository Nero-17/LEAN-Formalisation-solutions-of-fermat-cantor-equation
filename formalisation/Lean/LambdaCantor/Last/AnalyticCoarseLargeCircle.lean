import LambdaCantor.Last.AnalyticCoarseCircleGaps
import LambdaCantor.Last.AnalyticCoarseLargeSecant
import LambdaCantor.Last.OuterQuotient

noncomputable section
namespace LambdaCantor.Last

/-- A one-sided displacement by at most error enlarges any periodic empty
interval by at most error. The proof pulls back the interval trimmed at its
right endpoint, and does not assume continuity or surjectivity. -/
theorem one_sided_periodic_empty_pullback {source : Set ℝ}
    {first second : ℝ → ℝ} {period error left right : ℝ}
    (displacement : ∀ coordinate ∈ source,
      first coordinate ≤ second coordinate ∧ second coordinate ≤ first coordinate+error)
    (empty_interval : ∀ coordinate ∈ source, ∀ translate : ℤ,
      second coordinate+(translate : ℝ)*period ∉ Set.Ioo left right) :
    ∀ coordinate ∈ source, ∀ translate : ℤ,
      first coordinate+(translate : ℝ)*period ∉ Set.Ioo left (right-error) := by
  intro coordinate membership translate inside
  have bounds := displacement coordinate membership
  apply empty_interval coordinate membership translate
  constructor <;> linarith [inside.1, inside.2, bounds.1, bounds.2]

theorem large_logarithmic_copy_mem_outer_image {exponent ratio coordinate : ℝ} {depth : ℕ}
    (ratio_positive : 0 < ratio) (ratio_less_one : ratio < 1) (depth_positive : 0 < depth)
    (coordinate_mem : coordinate ∈ cantorSet ratio) :
    largeLogarithmicCopy exponent ratio depth coordinate ∈
      (fun value => exponent*Real.log value) '' outerCantor ratio := by
  have lower_copy : ∀ power : ℕ, ratio^power*coordinate ∈ cantorSet ratio := by
    intro power
    induction power with
    | zero => simpa using coordinate_mem
    | succ power induction =>
      convert low_copy_mem ratio_positive.le ratio_less_one induction using 1 <;>
        rw [pow_succ] <;> ring
  cases depth with
  | zero => omega
  | succ power =>
    refine ⟨1-ratio+ratio*(ratio^power*coordinate),
      ⟨ratio^power*coordinate, lower_copy power, rfl⟩, ?_⟩
    unfold largeLogarithmicCopy
    congr 2
    rw [pow_succ]
    ring

/-- Actual logarithmic-copy circle gaps, derived from the proved secant
error and the actual linear Cantor circle estimate. The only scale relation
is the defining identity βh = α log(1+λ^n/(1-λ)). -/
theorem large_logarithmic_copy_circle_gap_bound
    {exponent ratio scale period left right : ℝ} (depth : ℕ)
    (exponent_nonnegative : 0 ≤ exponent)
    (above_third : (1/3 : ℝ) ≤ ratio) (less_half : ratio < 1/2)
    (period_positive : 0 < period)
    (scale_lower : 1 ≤ scale) (scale_upper : scale < 1/ratio)
    (scale_identity : scale*period = exponent*Real.log (1+ratio^depth/(1-ratio)))
    (empty_arc : ∀ coordinate ∈ cantorSet ratio, ∀ translate : ℤ,
      largeLogarithmicCopy exponent ratio depth coordinate+(translate : ℝ)*period ∉
        Set.Ioo left right) :
    right-left ≤ period*max (1-2*ratio) (min (scale*(1-2*ratio)) (2-scale))+
      exponent*(ratio^depth/(1-ratio))^2/8 := by
  have ratio_positive : 0 < ratio := by linarith
  have ratio_less_one : ratio < 1 := by linarith
  have displacement : ∀ coordinate ∈ cantorSet ratio,
      exponent*Real.log (1-ratio)+period*scale*coordinate ≤
          largeLogarithmicCopy exponent ratio depth coordinate ∧
        largeLogarithmicCopy exponent ratio depth coordinate ≤
          exponent*Real.log (1-ratio)+period*scale*coordinate+
            exponent*(ratio^depth/(1-ratio))^2/8 := by
    intro coordinate membership
    have bounds := large_logarithmic_copy_secant_bounds depth exponent_nonnegative
      ratio_positive ratio_less_one (cantorSet_subset_unitInterval ratio_positive.le ratio_less_one membership)
    rw [mul_comm period scale, scale_identity]
    constructor <;> linarith [bounds.1, bounds.2]
  have trimmed_empty := one_sided_periodic_empty_pullback displacement empty_arc
  have normalized_empty : ScaledCantorCircleAvoids ratio scale
      ((left-exponent*Real.log (1-ratio))/period)
      ((right-exponent*(ratio^depth/(1-ratio))^2/8-exponent*Real.log (1-ratio))/period) := by
    intro coordinate membership translate inside
    apply trimmed_empty coordinate membership translate
    have lower := (div_lt_iff₀ period_positive).mp inside.1
    have upper := (lt_div_iff₀ period_positive).mp inside.2
    constructor <;> nlinarith
  have normalized_bound := scaled_cantor_circle_gap_bound above_third less_half
    scale_lower scale_upper normalized_empty
  have multiplied := mul_le_mul_of_nonneg_left normalized_bound period_positive.le
  have width_identity : period*
      ((right-exponent*(ratio^depth/(1-ratio))^2/8-exponent*Real.log (1-ratio))/period-
        (left-exponent*Real.log (1-ratio))/period) =
      right-left-exponent*(ratio^depth/(1-ratio))^2/8 := by
    field_simp [period_positive.ne']
    <;> ring
  rw [width_identity] at multiplied
  linarith

end LambdaCantor.Last
