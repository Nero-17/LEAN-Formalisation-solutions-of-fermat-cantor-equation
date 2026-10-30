import LambdaCantor.RationalPowers.RealNearAxisRegularity
import LambdaCantor.RationalPowers.FermatRoots
import LambdaCantor.Classical.GoodSlopeIsolation

noncomputable section
namespace LambdaCantor.RationalPowers
open Integer

theorem real_near_axis_isolated_coordinates_rational (exponent phase : ℝ)
    (exponent_ge_one : 1 ≤ exponent) (horizontalDepth verticalDepth : ℕ)
    (horizontal vertical scale : ℝ) (scale_nonzero : scale ≠ 0)
    (horizontal_positive : 0 < horizontal)
    (drop_positive : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < realPowerDrop exponent scale ((vertical+1-y)/3^verticalDepth))
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : Classical.CoordinateBounds
      (realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical scale)
      horizontalLower horizontalUpper verticalLower verticalUpper)
    (first_gap : verticalUpper ≤ horizontalLower) (middle_gap : horizontalUpper ≤ 3*verticalLower)
    (point : Classical.cantorLevel
      (realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical scale) 0)
    (vertical_derivative_positive : 0 < realNearAxisVertical exponent vertical scale point.val.2 verticalDepth)
    (good : GoodSlope ((exponent/(horizontal+point.val.1))/
      realNearAxisVertical exponent vertical scale point.val.2 verticalDepth))
    (isolated : IsOpen ({point} : Set (Classical.cantorLevel
      (realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical scale) 0))) :
    (∃ first : ℚ, (first : ℝ)=point.val.1) ∧
      (∃ second : ℚ, (second : ℝ)=point.val.2) := by
  obtain ⟨first, first_value⟩ := point.property.1.1
  obtain ⟨second, second_value⟩ := point.property.1.2
  have first_bounds := cantorSet_subset_unitInterval (by norm_num : (0 : ℝ) ≤ 1/3) (by norm_num)
    point.property.1.1
  have second_bounds := cantorSet_subset_unitInterval (by norm_num : (0 : ℝ) ≤ 1/3) (by norm_num)
    point.property.1.2
  obtain ⟨derivative, strict, formula⟩ := realNearAxisLog_hasStrictFDerivAt exponent_ge_one scale_nonzero
    horizontalDepth verticalDepth horizontal vertical point.val.1 point.val.2
    (by linarith [first_bounds.1]) (drop_positive _ second_bounds)
  obtain ⟨radius, radius_positive, ball⟩ := Metric.isOpen_iff.mp isolated point (by simp)
  have point_equation : (address (1/3) first,address (1/3) second)=point.val :=
    Prod.ext first_value second_value
  have isolated_ball : ∀ other ∈ Classical.cantorLevel
      (realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical scale)
      (realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical scale
        (address (1/3) first) (address (1/3) second)),
      dist other (address (1/3) first,address (1/3) second) < radius →
        other = (address (1/3) first,address (1/3) second) := by
    intro other membership close
    have other_member : other ∈ Classical.cantorLevel
        (realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical scale) 0 := by
      simpa only [first_value, second_value,
        (show realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical scale
          point.val.1 point.val.2 = 0 from point.property.2)] using membership
    have nearby : (⟨other,other_member⟩ : Classical.cantorLevel
        (realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical scale) 0)
        ∈ Metric.ball point radius := by
      change dist other point.val < radius
      simpa only [point_equation] using close
    have equality := congrArg Subtype.val (Set.mem_singleton_iff.mp (ball nearby))
    exact equality.trans point_equation.symm
  have rational := Classical.good_slope_isolated_coordinates_rational
    (realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical scale)
    (continuousOn_realNearAxisLog exponent_ge_one scale_nonzero horizontalDepth verticalDepth
      horizontal vertical horizontal_positive drop_positive)
    _ _ _ _ bounds first_gap middle_gap first second
    (exponent/(horizontal+point.val.1)) (realNearAxisVertical exponent vertical scale point.val.2 verticalDepth)
    vertical_derivative_positive good derivative
    (by simpa only [point_equation] using strict.hasFDerivAt) formula radius radius_positive isolated_ball
  obtain ⟨⟨rationalFirst,first_equal⟩,⟨rationalSecond,second_equal⟩⟩ := rational
  exact ⟨⟨rationalFirst,first_equal.trans first_value⟩,⟨rationalSecond,second_equal.trans second_value⟩⟩

/-- The proved rational-power descent and FLT exclude every isolated point of
an actual noncircle rational-exponent logarithmic source. The depths are
independent natural numbers with the exact rational phase relation. -/
theorem real_near_axis_no_isolated (numerator denominator : ℕ)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    (exponent_gt_one : 1 < (numerator : ℝ)/denominator)
    (exponent_ne_two : (numerator : ℝ)/denominator ≠ 2)
    (phase : ℝ) (horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical : ℕ)
    (phase_relation : phase = (secondDepth : ℝ)-((numerator : ℝ)/denominator)*firstDepth)
    (horizontal_positive : 0 < horizontal) (vertical_positive : 0 < vertical)
    (vertical_bound : vertical+1 ≤ 3^verticalDepth)
    (scale_small : (1/3 : ℝ)^secondDepth < 1)
    (drop_positive : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < realPowerDrop ((numerator : ℝ)/denominator) ((1/3 : ℝ)^secondDepth)
        ((vertical+1-y)/3^verticalDepth))
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : Classical.CoordinateBounds
      (realNearAxisLog ((numerator : ℝ)/denominator) phase horizontalDepth verticalDepth horizontal vertical
        ((1/3 : ℝ)^secondDepth)) horizontalLower horizontalUpper verticalLower verticalUpper)
    (first_gap : verticalUpper ≤ horizontalLower) (middle_gap : horizontalUpper ≤ 3*verticalLower)
    (slopes : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < realNearAxisVertical ((numerator : ℝ)/denominator) vertical ((1/3 : ℝ)^secondDepth) y verticalDepth ∧
      GoodSlope ((((numerator : ℝ)/denominator)/(horizontal+x))/
        realNearAxisVertical ((numerator : ℝ)/denominator) vertical ((1/3 : ℝ)^secondDepth) y verticalDepth)) :
    ∀ point : Classical.cantorLevel
      (realNearAxisLog ((numerator : ℝ)/denominator) phase horizontalDepth verticalDepth horizontal vertical
        ((1/3 : ℝ)^secondDepth)) 0, ¬ IsOpen ({point} : Set (Classical.cantorLevel
      (realNearAxisLog ((numerator : ℝ)/denominator) phase horizontalDepth verticalDepth horizontal vertical
        ((1/3 : ℝ)^secondDepth)) 0)) := by
  intro point isolated
  have horizontal_real_positive : (0 : ℝ) < horizontal := by exact_mod_cast horizontal_positive
  have vertical_real_positive : (0 : ℝ) < vertical := by exact_mod_cast vertical_positive
  have first_bounds := cantorSet_subset_unitInterval (by norm_num : (0 : ℝ) ≤ 1/3) (by norm_num)
    point.property.1.1
  have second_bounds := cantorSet_subset_unitInterval (by norm_num : (0 : ℝ) ≤ 1/3) (by norm_num)
    point.property.1.2
  have slope := slopes point.val.1 first_bounds point.val.2 second_bounds
  obtain ⟨⟨first,first_equal⟩,⟨second,second_equal⟩⟩ := real_near_axis_isolated_coordinates_rational
    ((numerator : ℝ)/denominator) phase exponent_gt_one.le horizontalDepth verticalDepth horizontal vertical
    ((1/3 : ℝ)^secondDepth) (by positivity) horizontal_real_positive drop_positive
    _ _ _ _ bounds first_gap middle_gap point slope.1 slope.2 isolated
  have u_positive : 0 < ((horizontal : ℝ)+point.val.1)/(3 : ℝ)^horizontalDepth := by
    exact div_pos (by linarith [first_bounds.1]) (by positivity)
  have v_upper : ((vertical : ℝ)+1-point.val.2)/(3 : ℝ)^verticalDepth ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < (3 : ℝ)^verticalDepth)).mpr
    have cast_bound : (vertical : ℝ)+1 ≤ (3 : ℝ)^verticalDepth := by exact_mod_cast vertical_bound
    linarith [second_bounds.1]
  have y_positive : 0 < 1-(1/3 : ℝ)^secondDepth*
      (((vertical : ℝ)+1-point.val.2)/(3 : ℝ)^verticalDepth) := by
    have multiplied := mul_le_mul_of_nonneg_left v_upper
      (show (0 : ℝ) ≤ (1/3 : ℝ)^secondDepth by positivity)
    nlinarith [scale_small]
  apply positive_rational_coordinates_not_on_real_fermat numerator denominator denominator_positive coprime
    exponent_gt_one exponent_ne_two
    ((1/3 : ℝ)^firstDepth*(((horizontal : ℝ)+point.val.1)/(3 : ℝ)^horizontalDepth))
    (1-(1/3 : ℝ)^secondDepth*(((vertical : ℝ)+1-point.val.2)/(3 : ℝ)^verticalDepth))
    (by positivity) y_positive
  · refine ⟨(1/3 : ℚ)^firstDepth*((horizontal+first)/3^horizontalDepth), ?_⟩
    push_cast
    rw [first_equal]
  · refine ⟨1-(1/3 : ℚ)^secondDepth*((vertical+1-second)/3^verticalDepth), ?_⟩
    push_cast
    rw [second_equal]
  · exact realNearAxisLog_zero_physical_equation ((numerator : ℝ)/denominator) phase
      horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical point.val.1 point.val.2
      phase_relation u_positive (drop_positive _ second_bounds) point.property.2

end LambdaCantor.RationalPowers

