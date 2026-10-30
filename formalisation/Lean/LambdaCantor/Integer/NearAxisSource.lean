import LambdaCantor.Integer.NearAxisPerfect
import LambdaCantor.Integer.NearAxisStrictSource
import LambdaCantor.Integer.IrrationalTangentSelection

namespace LambdaCantor.Integer

theorem cantorLevel_compact_on_unit (function : ℝ → ℝ → ℝ) (target : ℝ)
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
    simp only [Classical.cantorLevel,cantorSet_third_eq,Set.mem_inter_iff,Set.mem_setOf_eq]
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

/-- A strict source in any of the five certified bands yields a nonempty
compact exact Fermat source without isolated points, at integer cylinder depth.
Every hypothesis refers to the finite logarithmic source, not its unknown fibre. -/
theorem near_axis_perfect_source (n d p q P Q : ℕ) (a b : ℝ)
    (exponent : 3 ≤ n) (positiveP : 0 < P) (positiveQ : 0 < Q)
    (boundQ : Q+1 ≤ 3^q)
    (lowerBand : 1 < a) (upperBand : b < 3) (positiveB : 0 < b)
    (bandGood : ∀ slope : ℝ, a < slope → slope < b → GoodSlope slope)
    (lowerRatio : a/Q < (n : ℝ)/(P+1))
    (upperRatio : (n : ℝ)/P < b/(Q+1))
    (lowerCorner : nearAxisLog n d p q P Q 0 0 0 < 0)
    (upperCorner : 0 < nearAxisLog n d p q P Q 0 1 1) :
    ∃ k : ℕ,
      let source := Classical.cantorLevel (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0
      source.Nonempty ∧ IsCompact source ∧
      (∀ point : source, ¬ IsOpen ({point} : Set source)) ∧ ¬ source.Countable ∧
      (1/3 : ℝ)^(n*k+d) < 1 ∧
      (∀ y ∈ Set.Icc (0 : ℝ) 1,
        0 < ((Q+1-y)/3^q)*fermatQuotient n ((1/3 : ℝ)^(n*k+d)*((Q+1-y)/3^q))) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        0 < nearAxisVertical n q Q ((1/3 : ℝ)^(n*k+d)) y ∧
        GoodSlope (nearAxisHorizontal n P x/nearAxisVertical n q Q ((1/3 : ℝ)^(n*k+d)) y)) := by
  have positiveN : 0 < n := by omega
  have positivePReal : (0 : ℝ) < P := by exact_mod_cast positiveP
  have positiveQReal : (0 : ℝ) < Q := by exact_mod_cast positiveQ
  obtain ⟨verticalLower,verticalUpper,verticalPositive,firstGap,middleGap,eventualBounds⟩ :=
    near_axis_strict_bounds n d p q P Q a b positiveN positivePReal positiveQReal
      lowerBand upperBand positiveB lowerRatio upperRatio
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
  have nonempty : (Classical.cantorLevel (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0).Nonempty := by
    obtain ⟨first,second,firstMember,secondMember,equation⟩ :=
      Classical.general_cantor_level_local (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d)))
        bounds.1 _ _ _ _ bounds.2.1 firstGap middleGap 0 0 1 0
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by simpa using corners.1.le) (by simpa using corners.2.le)
    refine ⟨(first,second),?_,by simpa using equation⟩
    simpa only [cantorSet_third_eq,Set.mem_prod] using And.intro firstMember secondMember
  have compact := cantorLevel_compact_on_unit _ 0 bounds.1
  have noIsolated := near_axis_no_isolated n d p q k P Q exponent positiveP positiveQ boundQ small
    (fun y hy => (residual y hy).1) _ _ _ _ bounds.2.1 firstGap middleGap
    (fun x hx y hy => ⟨(bounds.2.2 x hx y hy).1,
      bandGood _ (bounds.2.2 x hx y hy).2.1 (bounds.2.2 x hx y hy).2.2⟩)
  exact ⟨k,nonempty,compact,noIsolated,
    compact_without_isolated_uncountable _ compact nonempty noIsolated,small,
    (fun y hy => (residual y hy).1),
    fun x hx y hy => ⟨(bounds.2.2 x hx y hy).1,
      bandGood _ (bounds.2.2 x hx y hy).2.1 (bounds.2.2 x hx y hy).2.2⟩⟩

end LambdaCantor.Integer
