import LambdaCantor.Integer.NearAxisPositiveDimension
import LambdaCantor.Integer.NearAxisReciprocalSource

namespace LambdaCantor.Integer

theorem cantorLevel_swap_nonisolated (function : ℝ → ℝ → ℝ) (level : ℝ)
    (point : Classical.cantorLevel function level)
    (nonisolated : ¬ IsOpen ({point} : Set (Classical.cantorLevel function level))) :
    ¬ IsOpen ({(⟨(point.val.2,point.val.1),⟨⟨point.property.1.2,point.property.1.1⟩,
      point.property.2⟩⟩ : Classical.cantorLevel (fun x y => function y x) level)} :
      Set (Classical.cantorLevel (fun x y => function y x) level)) := by
  let swapMap : Classical.cantorLevel function level →
      Classical.cantorLevel (fun x y => function y x) level := fun value =>
    ⟨(value.val.2,value.val.1),⟨⟨value.property.1.2,value.property.1.1⟩,value.property.2⟩⟩
  have continuousMap : Continuous swapMap :=
    (continuous_swap.comp continuous_subtype_val).subtype_mk _
  intro isolated
  have preimage := isolated.preimage continuousMap
  have equality : swapMap ⁻¹' {swapMap point} = {point} := by
    ext value
    simp only [Set.mem_preimage,Set.mem_singleton_iff]
    constructor
    · intro equal
      apply Subtype.ext
      have coordinates := congrArg Subtype.val equal
      apply Prod.ext
      · exact congrArg Prod.snd coordinates
      · exact congrArg Prod.fst coordinates
    · intro equal
      rw [equal]
  apply nonisolated
  rwa [equality] at preimage

theorem cantorLevel_swap_dimH (function : ℝ → ℝ → ℝ) (level : ℝ) :
    dimH (Classical.cantorLevel (fun x y => function y x) level) =
      dimH (Classical.cantorLevel function level) := by
  have isometry : Isometry (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
    Isometry.of_dist_eq (fun first second => by
      simp only [Prod.dist_eq]
      exact max_comm _ _)
  have equality : Prod.swap '' Classical.cantorLevel function level =
      Classical.cantorLevel (fun x y => function y x) level := by
    ext point
    constructor
    · rintro ⟨value,member,rfl⟩
      exact ⟨⟨member.1.2,member.1.1⟩,member.2⟩
    · intro member
      exact ⟨(point.2,point.1),⟨⟨member.1.2,member.1.1⟩,member.2⟩,rfl⟩
  rw [← equality]
  exact isometry.dimH_image _

theorem reciprocal_strict_log_source_positive_dimension (n d p q P Q : ℕ) (a b : ℝ)
    (exponent : 3 ≤ n) (positiveP : 0 < P) (positiveQ : 0 < Q)
    (prefixP : ternaryPrefix P p = true) (prefixQ : ternaryPrefix Q q = true)
    (boundQ : Q+1 ≤ 3^q)
    (lowerBand : 1/3 < a) (upperBand : b < 1) (positiveB : 0 < b)
    (bandGood : ∀ slope : ℝ, 1/b < slope → slope < 1/a → GoodSlope slope)
    (lowerRatio : a/Q < (n : ℝ)/(P+1))
    (upperRatio : (n : ℝ)/P < b/(Q+1))
    (lowerCorner : nearAxisLog n d p q P Q 0 0 0 < 0)
    (upperCorner : 0 < nearAxisLog n d p q P Q 0 1 1) :
    0 < dimH (intersection (n : ℝ) (1/3)) := by
  obtain ⟨k,_,_,nonisolated,uncountable,small,residual,slopes⟩ := near_axis_reciprocal_perfect_source
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
  have firstBounds := _root_.cantorSet_subset_unitInterval firstCantor
  have secondBounds := _root_.cantorSet_subset_unitInterval secondCantor
  have positivePReal : (0 : ℝ) < P := by exact_mod_cast positiveP
  have horizontalPositive : 0 < nearAxisHorizontal n P point.1 := by
    unfold nearAxisHorizontal
    apply div_pos (by exact_mod_cast (show 0 < n by omega))
    linarith [firstBounds.1]
  obtain ⟨derivative,strict,formula⟩ := nearAxisLog_swap_hasStrictFDerivAt
    n d p q P Q ((1/3 : ℝ)^(n*k+d)) point.1 point.2
      (by linarith [firstBounds.1]) (residual _ secondBounds)
  have dimension := good_slope_positive_dimension_of_derivative
    (fun value : ℝ × ℝ => nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d)) value.2 value.1)
    0 _ _ horizontalPositive (slopes _ firstBounds _ secondBounds) irrational
    ⟨(point.2,point.1),⟨⟨member.1.2,member.1.1⟩,member.2⟩⟩
    (cantorLevel_swap_nonisolated _ 0 ⟨point,member⟩ (nonisolated ⟨point,member⟩))
    derivative strict formula
  change 0 < dimH (Classical.cantorLevel
    (fun x y => nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d)) y x) 0) at dimension
  rw [cantorLevel_swap_dimH] at dimension
  exact dimension.trans_le (near_axis_dimension_le_intersection n d p q k P Q positiveP positiveQ
    boundQ prefixP prefixQ small residual)

end LambdaCantor.Integer

