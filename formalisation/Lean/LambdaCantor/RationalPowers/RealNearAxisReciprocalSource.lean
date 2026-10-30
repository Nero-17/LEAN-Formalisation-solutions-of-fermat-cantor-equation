import LambdaCantor.RationalPowers.RealNearAxisSource
import LambdaCantor.RationalPowers.RealNearAxisRatioBounds
import LambdaCantor.RationalPowers.RealNearAxisReciprocalPerfect

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.RationalPowers
open Integer

/-- Exact rational phase depths, genuine real-power C1 transfer, finite-stage
coverage and the rational-point obstruction construct an actual compact
perfect source. No integer-exponent source theorem is applied to a/b. -/
theorem real_near_axis_reciprocal_perfect_source (numerator denominator : ℕ) (phaseNumerator : ℤ)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    (exponent_gt_one : 1 < (numerator : ℝ)/denominator)
    (exponent_ne_two : (numerator : ℝ)/denominator ≠ 2)
    (horizontalDepth verticalDepth horizontal vertical : ℕ) (lowerBand upperBand : ℝ)
    (horizontal_positive : 0 < horizontal) (vertical_positive : 0 < vertical)
    (vertical_bound : vertical+1 ≤ 3^verticalDepth)
    (band_lower : 1/3 < lowerBand) (band_upper : upperBand < 1) (upper_positive : 0 < upperBand)
    (band_good : ∀ slope : ℝ, 1/upperBand < slope → slope < 1/lowerBand → GoodSlope slope)
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
        GoodSlope (realNearAxisVertical ((numerator : ℝ)/denominator) vertical ((1/3 : ℝ)^secondDepth) y verticalDepth/
          (((numerator : ℝ)/denominator)/(horizontal+x)))) := by
  have horizontal_real_positive : (0 : ℝ) < horizontal := by exact_mod_cast horizontal_positive
  have vertical_real_positive : (0 : ℝ) < vertical := by exact_mod_cast vertical_positive
  have vertical_real_bound : (vertical : ℝ)+1 ≤ (3 : ℝ)^verticalDepth := by exact_mod_cast vertical_bound
  have exponent_positive : 0 < (numerator : ℝ)/denominator := by linarith
  have numerator_positive : 0 < numerator := by
    have numerator_real_positive : (0 : ℝ) < numerator :=
      (div_pos_iff_of_pos_right (by exact_mod_cast denominator_positive : (0 : ℝ) < denominator)).mp exponent_positive
    exact_mod_cast numerator_real_positive
  obtain ⟨verticalLower, verticalUpper, delta, vertical_lower_positive, vertical_upper_positive,
    lower_strong, upper_strong, delta_positive, uniform⟩ := real_near_axis_ratio_bounds
      ((numerator : ℝ)/denominator) ((phaseNumerator : ℝ)/denominator)
      horizontalDepth verticalDepth horizontal vertical lowerBand upperBand exponent_gt_one
      horizontal_real_positive vertical_real_positive vertical_real_bound (by linarith) upper_positive
      lower_ratio upper_ratio
  have first_gap : ((numerator : ℝ)/denominator)/horizontal ≤ verticalLower := by nlinarith
  have middle_gap : verticalUpper ≤ 3*(((numerator : ℝ)/denominator)/(horizontal+1)) := by nlinarith
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
  have inverse_good : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      GoodSlope (realNearAxisVertical ((numerator : ℝ)/denominator) vertical
        ((1/3 : ℝ)^(secondDepth index)) y verticalDepth/(((numerator : ℝ)/denominator)/(horizontal+x))) := by
    intro x hx y hy
    have ratios := bounds.2.2.2 x hx y hy
    have horizontal_derivative_positive : 0 < ((numerator : ℝ)/denominator)/(horizontal+x) :=
      div_pos exponent_positive (by linarith [hx.1])
    apply band_good
    · apply (div_lt_div_iff₀ upper_positive horizontal_derivative_positive).mpr
      have multiplied := (div_lt_iff₀ ratios.1).mp ratios.2.2
      nlinarith
    · apply (div_lt_div_iff₀ horizontal_derivative_positive (by linarith : 0 < lowerBand)).mpr
      have multiplied := (lt_div_iff₀ ratios.1).mp ratios.2.1
      nlinarith
  have nonempty : (Classical.cantorLevel
      (realNearAxisLog ((numerator : ℝ)/denominator) ((phaseNumerator : ℝ)/denominator)
        horizontalDepth verticalDepth horizontal vertical ((1/3 : ℝ)^(secondDepth index))) 0).Nonempty := by
    obtain ⟨first, second, first_member, second_member, equation⟩ :=
      Classical.general_cantor_level_local
        (fun x y => realNearAxisLog ((numerator : ℝ)/denominator) ((phaseNumerator : ℝ)/denominator)
          horizontalDepth verticalDepth horizontal vertical ((1/3 : ℝ)^(secondDepth index)) y x)
        (continuousOn_swap _ bounds.1) _ _ _ _ (coordinateBounds_swap _ _ _ _ _ bounds.2.1)
        first_gap middle_gap 0 0 1 0
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by simpa using lower_at.le) (by simpa using upper_at.le)
    exact ⟨(second,first), ⟨by simpa only [cantorSet_third_eq,Set.mem_prod] using And.intro second_member first_member,
      by simpa using equation⟩⟩
  have compact := real_cantor_level_compact_on_unit _ 0 bounds.1
  have no_isolated := real_near_axis_reciprocal_no_isolated numerator denominator denominator_positive coprime
    exponent_gt_one exponent_ne_two ((phaseNumerator : ℝ)/denominator)
    horizontalDepth verticalDepth (firstDepth index) (secondDepth index) horizontal vertical (phases index).symm
    horizontal_positive vertical_positive vertical_bound small bounds.2.2.1
    _ _ _ _ bounds.2.1 first_gap middle_gap
    (fun x hx y hy => ⟨(bounds.2.2.2 x hx y hy).1,
      inverse_good x hx y hy⟩)
  exact ⟨firstDepth index, secondDepth index, (phases index).symm, nonempty, compact, no_isolated,
    compact_without_isolated_uncountable _ compact nonempty no_isolated, small, bounds.2.2.1,
    fun x hx y hy => ⟨(bounds.2.2.2 x hx y hy).1,
      inverse_good x hx y hy⟩⟩




end LambdaCantor.RationalPowers
