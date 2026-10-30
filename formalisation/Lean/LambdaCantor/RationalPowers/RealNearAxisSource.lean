import LambdaCantor.RationalPowers.RealNearAxisStrictSource
import LambdaCantor.RationalPowers.RealNearAxisPerfect
import LambdaCantor.RationalPowers.PhaseDepths
import LambdaCantor.Integer.IrrationalTangentSelection
import LambdaCantor.Classical.GeneralCoverLocal

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.RationalPowers
open Integer

theorem real_cantor_level_compact_on_unit (function : ℝ → ℝ → ℝ) (target : ℝ)
    (continuous : ContinuousOn (fun point : ℝ × ℝ => function point.1 point.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :
    IsCompact (Classical.cantorLevel function target) := by
  have compact := (_root_.isCompact_cantorSet.prod _root_.isCompact_cantorSet).inter_right
    (isClosed_eq (Classical.continuous_clamped function continuous)
      (continuous_const : Continuous (fun _ : ℝ × ℝ => target)))
  have equality : (_root_.cantorSet ×ˢ _root_.cantorSet) ∩
      {point : ℝ × ℝ | function (Classical.unitClamp point.1) (Classical.unitClamp point.2)=target} =
      Classical.cantorLevel function target := by
    ext point
    simp only [Classical.cantorLevel, cantorSet_third_eq, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor <;> intro member
    · refine ⟨member.1, ?_⟩
      simpa only [
        Classical.unitClamp_eq point.1 (_root_.cantorSet_subset_unitInterval member.1.1),
        Classical.unitClamp_eq point.2 (_root_.cantorSet_subset_unitInterval member.1.2)]
        using member.2
    · refine ⟨member.1, ?_⟩
      simpa only [
        Classical.unitClamp_eq point.1 (_root_.cantorSet_subset_unitInterval member.1.1),
        Classical.unitClamp_eq point.2 (_root_.cantorSet_subset_unitInterval member.1.2)]
        using member.2
  rwa [equality] at compact

/-- Exact rational phase depths, genuine real-power C1 transfer, finite-stage
coverage and the rational-point obstruction construct an actual compact
perfect source. No integer-exponent source theorem is applied to a/b. -/
theorem real_near_axis_perfect_source (numerator denominator : ℕ) (phaseNumerator : ℤ)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    (exponent_gt_one : 1 < (numerator : ℝ)/denominator)
    (exponent_ne_two : (numerator : ℝ)/denominator ≠ 2)
    (horizontalDepth verticalDepth horizontal vertical : ℕ) (lowerBand upperBand : ℝ)
    (horizontal_positive : 0 < horizontal) (vertical_positive : 0 < vertical)
    (vertical_bound : vertical+1 ≤ 3^verticalDepth)
    (band_lower : 1 < lowerBand) (band_upper : upperBand < 3) (upper_positive : 0 < upperBand)
    (band_good : ∀ slope : ℝ, lowerBand < slope → slope < upperBand → GoodSlope slope)
    (lower_ratio : lowerBand/vertical < ((numerator : ℝ)/denominator)/(horizontal+1))
    (upper_ratio : ((numerator : ℝ)/denominator)/horizontal < upperBand/(vertical+1))
    (lower_corner : ((phaseNumerator : ℝ)/denominator)*Real.log 3+
      ((numerator : ℝ)/denominator)*Real.log ((horizontal : ℝ)/3^horizontalDepth)-
        Real.log ((numerator : ℝ)/denominator)-Real.log ((vertical+1 : ℝ)/3^verticalDepth) < 0)
    (upper_corner : 0 < ((phaseNumerator : ℝ)/denominator)*Real.log 3+
      ((numerator : ℝ)/denominator)*Real.log ((horizontal+1 : ℝ)/3^horizontalDepth)-
        Real.log ((numerator : ℝ)/denominator)-Real.log ((vertical : ℝ)/3^verticalDepth)) :
    ∃ firstDepth secondDepth : ℕ,
      ((phaseNumerator : ℝ)/denominator) = (secondDepth : ℝ)-
        ((numerator : ℝ)/denominator)*firstDepth ∧
      let source := Classical.cantorLevel
        (realNearAxisLog ((numerator : ℝ)/denominator) ((phaseNumerator : ℝ)/denominator)
          horizontalDepth verticalDepth horizontal vertical ((1/3 : ℝ)^secondDepth)) 0
      source.Nonempty ∧ IsCompact source ∧
      (∀ point : source, ¬ IsOpen ({point} : Set source)) ∧ ¬ source.Countable ∧
      (1/3 : ℝ)^secondDepth < 1 ∧
      (∀ y ∈ Set.Icc (0 : ℝ) 1,
        0 < realPowerDrop ((numerator : ℝ)/denominator) ((1/3 : ℝ)^secondDepth)
          ((vertical+1-y)/3^verticalDepth)) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        0 < realNearAxisVertical ((numerator : ℝ)/denominator) vertical ((1/3 : ℝ)^secondDepth) y verticalDepth ∧
        GoodSlope ((((numerator : ℝ)/denominator)/(horizontal+x))/
          realNearAxisVertical ((numerator : ℝ)/denominator) vertical ((1/3 : ℝ)^secondDepth) y verticalDepth)) := by
  have horizontal_real_positive : (0 : ℝ) < horizontal := by exact_mod_cast horizontal_positive
  have vertical_real_positive : (0 : ℝ) < vertical := by exact_mod_cast vertical_positive
  have vertical_real_bound : (vertical : ℝ)+1 ≤ (3 : ℝ)^verticalDepth := by exact_mod_cast vertical_bound
  have exponent_positive : 0 < (numerator : ℝ)/denominator := by linarith
  have numerator_positive : 0 < numerator := by
    have numerator_real_positive : (0 : ℝ) < numerator :=
      (div_pos_iff_of_pos_right (by exact_mod_cast denominator_positive : (0 : ℝ) < denominator)).mp exponent_positive
    exact_mod_cast numerator_real_positive
  obtain ⟨verticalLower, verticalUpper, delta, vertical_lower_positive, first_gap,
    middle_gap, delta_positive, uniform⟩ := real_near_axis_strict_bounds
      ((numerator : ℝ)/denominator) ((phaseNumerator : ℝ)/denominator)
      horizontalDepth verticalDepth horizontal vertical lowerBand upperBand exponent_gt_one
      horizontal_real_positive vertical_real_positive vertical_real_bound band_lower band_upper upper_positive
      lower_ratio upper_ratio
  obtain ⟨firstDepth, secondDepth, first_limit, second_limit, phases⟩ :=
    rational_phase_depth_sequences numerator denominator phaseNumerator coprime numerator_positive denominator_positive
  have scale_limit := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1/3) (by norm_num)).comp second_limit
  have scale_within : Tendsto (fun index => (1/3 : ℝ)^(secondDepth index)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ scale_limit
      (Eventually.of_forall (fun index => by
        change 0 < (1/3 : ℝ)^(secondDepth index)
        positivity))
  have lower_limit := (realNearAxisLog_limit ((numerator : ℝ)/denominator) ((phaseNumerator : ℝ)/denominator)
    exponent_positive horizontalDepth verticalDepth horizontal vertical 0 0 (by linarith)).comp scale_within
  have upper_limit := (realNearAxisLog_limit ((numerator : ℝ)/denominator) ((phaseNumerator : ℝ)/denominator)
    exponent_positive horizontalDepth verticalDepth horizontal vertical 1 1 (by linarith)).comp scale_within
  simp only [add_zero, sub_zero] at lower_limit
  simp only [add_sub_cancel_right] at upper_limit
  have lower_eventual := lower_limit.eventually (Iio_mem_nhds lower_corner)
  have upper_eventual := upper_limit.eventually (Ioi_mem_nhds upper_corner)
  have scale_eventual := scale_limit.eventually (Iio_mem_nhds (lt_min delta_positive (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨index, lower_at, upper_at, small_at⟩ := (lower_eventual.and (upper_eventual.and scale_eventual)).exists
  have scale_positive : 0 < (1/3 : ℝ)^(secondDepth index) := by positivity
  have bounds := uniform ((1/3 : ℝ)^(secondDepth index)) scale_positive
    (small_at.trans_le (min_le_left _ _))
  have small : (1/3 : ℝ)^(secondDepth index) < 1 := small_at.trans_le (min_le_right _ _)
  have nonempty : (Classical.cantorLevel
      (realNearAxisLog ((numerator : ℝ)/denominator) ((phaseNumerator : ℝ)/denominator)
        horizontalDepth verticalDepth horizontal vertical ((1/3 : ℝ)^(secondDepth index))) 0).Nonempty := by
    obtain ⟨first, second, first_member, second_member, equation⟩ :=
      Classical.general_cantor_level_local
        (realNearAxisLog ((numerator : ℝ)/denominator) ((phaseNumerator : ℝ)/denominator)
          horizontalDepth verticalDepth horizontal vertical ((1/3 : ℝ)^(secondDepth index)))
        bounds.1 _ _ _ _ bounds.2.1 first_gap middle_gap 0 0 1 0
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by simpa using lower_at.le) (by simpa using upper_at.le)
    refine ⟨(first,second), ?_, by simpa using equation⟩
    simpa only [cantorSet_third_eq, Set.mem_prod] using And.intro first_member second_member
  have compact := real_cantor_level_compact_on_unit _ 0 bounds.1
  have no_isolated := real_near_axis_no_isolated numerator denominator denominator_positive coprime
    exponent_gt_one exponent_ne_two ((phaseNumerator : ℝ)/denominator)
    horizontalDepth verticalDepth (firstDepth index) (secondDepth index) horizontal vertical (phases index).symm
    horizontal_positive vertical_positive vertical_bound small bounds.2.2.1
    _ _ _ _ bounds.2.1 first_gap middle_gap
    (fun x hx y hy => ⟨(bounds.2.2.2 x hx y hy).1,
      band_good _ (bounds.2.2.2 x hx y hy).2.1 (bounds.2.2.2 x hx y hy).2.2⟩)
  exact ⟨firstDepth index, secondDepth index, (phases index).symm, nonempty, compact, no_isolated,
    compact_without_isolated_uncountable _ compact nonempty no_isolated, small, bounds.2.2.1,
    fun x hx y hy => ⟨(bounds.2.2.2 x hx y hy).1,
      band_good _ (bounds.2.2.2 x hx y hy).2.1 (bounds.2.2.2 x hx y hy).2.2⟩⟩

end LambdaCantor.RationalPowers

