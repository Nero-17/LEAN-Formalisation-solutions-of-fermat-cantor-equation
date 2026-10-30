import LambdaCantor.Integer.NearAxisSwap
import LambdaCantor.Integer.NearAxisNormalizedTangent

namespace LambdaCantor.Integer

theorem near_axis_reciprocal_perfect_source (n d p q P Q : ℕ) (a b : ℝ)
    (exponent : 3 ≤ n) (positiveP : 0 < P) (positiveQ : 0 < Q)
    (boundQ : Q+1 ≤ 3^q)
    (lowerBand : 1/3 < a) (upperBand : b < 1) (positiveB : 0 < b)
    (bandGood : ∀ slope : ℝ, 1/b < slope → slope < 1/a → GoodSlope slope)
    (lowerRatio : a/Q < (n : ℝ)/(P+1))
    (upperRatio : (n : ℝ)/P < b/(Q+1))
    (lowerCorner : nearAxisLog n d p q P Q 0 0 0 < 0)
    (upperCorner : 0 < nearAxisLog n d p q P Q 0 1 1) :
    ∃ k : ℕ,
      let source := Classical.cantorLevel (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0
      source.Nonempty ∧ IsCompact source ∧
      (∀ point : source, ¬ IsOpen ({point} : Set source)) ∧ ¬ source.Countable ∧
      (1/3 : ℝ)^(n*k+d) < 1 ∧
      (∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < ((Q+1-y)/3^q)*
        fermatQuotient n ((1/3 : ℝ)^(n*k+d)*((Q+1-y)/3^q))) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        GoodSlope (nearAxisVertical n q Q ((1/3 : ℝ)^(n*k+d)) y/nearAxisHorizontal n P x)) := by
  have positiveN : 0 < n := by omega
  have positivePReal : (0 : ℝ) < P := by exact_mod_cast positiveP
  have positiveQReal : (0 : ℝ) < Q := by exact_mod_cast positiveQ
  have positiveA : 0 < a := by linarith
  obtain ⟨verticalLower,verticalUpper,verticalPositive,firstStrong,middleStrong,eventualBounds⟩ :=
    near_axis_ratio_bounds n d p q P Q a b positiveN positivePReal positiveQReal
      positiveA positiveB lowerRatio upperRatio
  have firstGap : (n : ℝ)/P ≤ verticalLower := by nlinarith
  have middleGap : verticalUpper ≤ 3*((n : ℝ)/(P+1)) := by
    have upperPositive : 0 < verticalUpper := by
      have bounds := eventualBounds.self_of_nhds
      have increments := bounds.2.1.vertical 0 (by norm_num) 0 (by norm_num) 1 (by norm_num) (by norm_num)
      nlinarith
    nlinarith
  have decay := near_axis_scale_tendsto n d positiveN
  have boundsEventual := decay.eventually eventualBounds
  have residualEventual := decay.eventually (nearAxisVertical_uniform n q positiveN Q 1
    positiveQReal (by norm_num))
  have cornersEventual := decay.eventually (nearAxisLog_corners_persist n d p q P Q
    positiveN positiveQReal lowerCorner upperCorner)
  have smallEventual : ∀ᶠ k : ℕ in Filter.atTop, (1/3 : ℝ)^(n*k+d) < 1 :=
    decay.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨k,bounds,residual,corners,small⟩ :=
    (boundsEventual.and (residualEventual.and (cornersEventual.and smallEventual))).exists
  have inverseGood : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      GoodSlope (nearAxisVertical n q Q ((1/3 : ℝ)^(n*k+d)) y/nearAxisHorizontal n P x) := by
    intro x hx y hy
    have ratios := bounds.2.2 x hx y hy
    have horizontalPositive : 0 < nearAxisHorizontal n P x := by
      unfold nearAxisHorizontal
      exact div_pos (by exact_mod_cast positiveN) (by linarith [hx.1])
    apply bandGood
    · apply (div_lt_div_iff₀ positiveB horizontalPositive).2
      have multiplied := (div_lt_iff₀ ratios.1).1 ratios.2.2
      nlinarith
    · apply (div_lt_div_iff₀ horizontalPositive positiveA).2
      have multiplied := (lt_div_iff₀ ratios.1).1 ratios.2.1
      nlinarith
  have nonempty : (Classical.cantorLevel (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0).Nonempty := by
    obtain ⟨first,second,firstMember,secondMember,equation⟩ :=
      Classical.general_cantor_level_local
        (fun x y => nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d)) y x)
        (continuousOn_swap _ bounds.1) _ _ _ _
        (coordinateBounds_swap _ _ _ _ _ bounds.2.1) firstGap middleGap 0 0 1 0
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by simpa using corners.1.le) (by simpa using corners.2.le)
    refine ⟨(second,first),?_,by simpa using equation⟩
    simpa only [Set.mem_prod,cantorSet_third_eq] using And.intro secondMember firstMember
  have compact := cantorLevel_compact_on_unit _ 0 bounds.1
  have noIsolated := near_axis_reciprocal_no_isolated n d p q k P Q exponent positiveP positiveQ
    boundQ small (fun y hy => (residual y hy).1) _ _ _ _ bounds.2.1 firstGap middleGap
    (fun x hx y hy => ⟨(bounds.2.2 x hx y hy).1,inverseGood x hx y hy⟩)
  exact ⟨k,nonempty,compact,noIsolated,
    compact_without_isolated_uncountable _ compact nonempty noIsolated,small,
    (fun y hy => (residual y hy).1),inverseGood⟩

theorem reciprocal_strict_log_source_normalized_irrational_tangent
    (n d p q P Q : ℕ) (a b : ℝ)
    (exponent : 3 ≤ n) (positiveP : 0 < P) (positiveQ : 0 < Q)
    (boundQ : Q+1 ≤ 3^q)
    (lowerBand : 1/3 < a) (upperBand : b < 1) (positiveB : 0 < b)
    (bandGood : ∀ slope : ℝ, 1/b < slope → slope < 1/a → GoodSlope slope)
    (lowerRatio : a/Q < (n : ℝ)/(P+1))
    (upperRatio : (n : ℝ)/P < b/(Q+1))
    (lowerCorner : nearAxisLog n d p q P Q 0 0 0 < 0)
    (upperCorner : 0 < nearAxisLog n d p q P Q 0 1 1) :
    ∃ k : ℕ, ∃ point ∈ Classical.cantorLevel
      (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0,
      GoodSlope (nearAxisVertical n q Q ((1/3 : ℝ)^(n*k+d)) point.2/nearAxisHorizontal n P point.1) ∧
      ∀ rational : ℚ, nearAxisVertical n q Q ((1/3 : ℝ)^(n*k+d)) point.2/
        nearAxisHorizontal n P point.1 ≠ (rational : ℝ) := by
  obtain ⟨k,_,_,_,uncountable,small,residual,slopes⟩ := near_axis_reciprocal_perfect_source
    n d p q P Q a b exponent positiveP positiveQ boundQ lowerBand upperBand positiveB bandGood
      lowerRatio upperRatio lowerCorner upperCorner
  have injective := near_axis_normalized_tangent_injective n d p q k P Q exponent
    positiveP positiveQ boundQ small residual
  have reciprocalInjective : Set.InjOn (fun point : ℝ × ℝ =>
      nearAxisVertical n q Q ((1/3 : ℝ)^(n*k+d)) point.2/nearAxisHorizontal n P point.1)
      (Classical.cantorLevel (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0) := by
    intro first firstMember second secondMember equality
    apply injective firstMember secondMember
    have inverted := congrArg (fun value : ℝ => value⁻¹) equality
    simpa only [inv_div] using inverted
  obtain ⟨point,member,irrational⟩ := exists_irrational_tangent _ uncountable _ reciprocalInjective
  have firstCantor : point.1 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]; exact member.1.1
  have secondCantor : point.2 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]; exact member.1.2
  exact ⟨k,point,member,slopes _ (_root_.cantorSet_subset_unitInterval firstCantor)
    _ (_root_.cantorSet_subset_unitInterval secondCantor),irrational⟩

end LambdaCantor.Integer
