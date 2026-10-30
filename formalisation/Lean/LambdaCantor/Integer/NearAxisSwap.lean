import LambdaCantor.Integer.NearAxisPerfect

namespace LambdaCantor.Integer

theorem coordinateBounds_swap (function : ℝ → ℝ → ℝ) (a b c d : ℝ)
    (bounds : Classical.CoordinateBounds function a b c d) :
    Classical.CoordinateBounds (fun x y => function y x) c d a b :=
  ⟨bounds.vertical,bounds.horizontal⟩

theorem continuousOn_swap (function : ℝ → ℝ → ℝ)
    (continuous : ContinuousOn (fun point : ℝ × ℝ => function point.1 point.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun point : ℝ × ℝ => function point.2 point.1)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
  continuous.comp (continuous_snd.prodMk continuous_fst).continuousOn
    (fun _ membership => ⟨membership.2,membership.1⟩)

theorem near_axis_reciprocal_isolated_rational (n d p q : ℕ) (P Q scale : ℝ)
    (positiveP : 0 < P)
    (positiveResidual : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < ((Q+1-y)/3^q)*fermatQuotient n (scale*((Q+1-y)/3^q)))
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : Classical.CoordinateBounds (nearAxisLog n d p q P Q scale)
      horizontalLower horizontalUpper verticalLower verticalUpper)
    (firstGap : horizontalUpper ≤ verticalLower) (middleGap : verticalUpper ≤ 3*horizontalLower)
    (point : Classical.cantorLevel (nearAxisLog n d p q P Q scale) 0)
    (horizontalPositive : 0 < nearAxisHorizontal n P point.val.1)
    (good : GoodSlope (nearAxisVertical n q Q scale point.val.2/nearAxisHorizontal n P point.val.1))
    (isolated : IsOpen ({point} : Set (Classical.cantorLevel (nearAxisLog n d p q P Q scale) 0))) :
    (∃ first : ℚ, (first : ℝ)=point.val.1) ∧
      (∃ second : ℚ, (second : ℝ)=point.val.2) := by
  obtain ⟨first,firstValue⟩ := point.property.1.1
  obtain ⟨second,secondValue⟩ := point.property.1.2
  have firstMember : point.val.1 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]; exact ⟨first,firstValue⟩
  have secondMember : point.val.2 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]; exact ⟨second,secondValue⟩
  have firstBounds := _root_.cantorSet_subset_unitInterval firstMember
  have secondBounds := _root_.cantorSet_subset_unitInterval secondMember
  obtain ⟨derivative,differentiable,formula⟩ := nearAxisLog_hasFDerivAt n d p q P Q scale
    point.val.1 point.val.2 (by linarith [firstBounds.1]) (positiveResidual _ secondBounds)
  have swapDerivative :=
    (hasFDerivAt_snd : HasFDerivAt (fun pair : ℝ × ℝ => pair.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (point.val.2,point.val.1)).prodMk
    (hasFDerivAt_fst : HasFDerivAt (fun pair : ℝ × ℝ => pair.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (point.val.2,point.val.1))
  have swappedDifferentiable := differentiable.comp (point.val.2,point.val.1) swapDerivative
  obtain ⟨radius,radiusPositive,ball⟩ := Metric.isOpen_iff.mp isolated point (by simp)
  have isolatedBall : ∀ other ∈ Classical.cantorLevel
      (fun x y => nearAxisLog n d p q P Q scale y x)
      (nearAxisLog n d p q P Q scale (address (1/3) first) (address (1/3) second)),
      dist other (address (1/3) second,address (1/3) first) < radius →
        other = (address (1/3) second,address (1/3) first) := by
    intro other membership close
    have originalMember : (other.2,other.1) ∈ Classical.cantorLevel
        (nearAxisLog n d p q P Q scale) 0 := by
      exact ⟨⟨membership.1.2,membership.1.1⟩,
        by simpa only [Set.mem_setOf_eq,firstValue,secondValue,
          show nearAxisLog n d p q P Q scale point.val.1 point.val.2 = 0 from point.property.2]
          using membership.2⟩
    have nearby : (⟨(other.2,other.1),originalMember⟩ : Classical.cantorLevel
        (nearAxisLog n d p q P Q scale) 0) ∈ Metric.ball point radius := by
      change dist (other.2,other.1) point.val < radius
      simpa only [Prod.dist_eq,firstValue,secondValue,max_comm] using close
    have equality := congrArg Subtype.val (Set.mem_singleton_iff.mp (ball nearby))
    apply Prod.ext
    · exact (congrArg Prod.snd equality).trans secondValue.symm
    · exact (congrArg Prod.fst equality).trans firstValue.symm
  have rational := Classical.good_slope_isolated_coordinates_rational
    (fun x y => nearAxisLog n d p q P Q scale y x)
    (continuousOn_swap _ (continuousOn_nearAxisLog n d p q P Q scale positiveP positiveResidual))
    _ _ _ _ (coordinateBounds_swap _ _ _ _ _ bounds) firstGap middleGap second first
    (nearAxisVertical n q Q scale point.val.2) (nearAxisHorizontal n P point.val.1)
    horizontalPositive good
    (derivative.comp ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)))
    (by
      have swappedLittle := HasFDerivAtFilter.isLittleOTVS swappedDifferentiable
      apply HasFDerivAtFilter.of_isLittleOTVS
      with_reducible_and_instances simpa only [Function.comp_apply,firstValue,secondValue]
        using swappedLittle)
    (by
      intro direction
      simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.coe_snd',ContinuousLinearMap.coe_fst',formula]
      ring)
    radius radiusPositive isolatedBall
  obtain ⟨⟨rationalSecond,secondEqual⟩,⟨rationalFirst,firstEqual⟩⟩ := rational
  exact ⟨⟨rationalFirst,firstEqual.trans firstValue⟩,⟨rationalSecond,secondEqual.trans secondValue⟩⟩

theorem near_axis_reciprocal_no_isolated (n d p q k P Q : ℕ) (exponent : 3 ≤ n)
    (positiveP : 0 < P) (positiveQ : 0 < Q) (boundQ : Q+1 ≤ 3^q)
    (small : (1/3 : ℝ)^(n*k+d) < 1)
    (positiveResidual : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < ((Q+1-y)/3^q)*fermatQuotient n ((1/3 : ℝ)^(n*k+d)*((Q+1-y)/3^q)))
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : Classical.CoordinateBounds (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d)))
      horizontalLower horizontalUpper verticalLower verticalUpper)
    (firstGap : horizontalUpper ≤ verticalLower) (middleGap : verticalUpper ≤ 3*horizontalLower)
    (slopes : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < nearAxisVertical n q Q ((1/3 : ℝ)^(n*k+d)) y ∧
      GoodSlope (nearAxisVertical n q Q ((1/3 : ℝ)^(n*k+d)) y/nearAxisHorizontal n P x)) :
    ∀ point : Classical.cantorLevel (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0,
      ¬ IsOpen ({point} : Set (Classical.cantorLevel
        (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0)) := by
  intro point isolated
  have positivePReal : (0 : ℝ) < P := by exact_mod_cast positiveP
  have positiveQReal : (0 : ℝ) < Q := by exact_mod_cast positiveQ
  have firstMember : point.val.1 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]; exact point.property.1.1
  have secondMember : point.val.2 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]; exact point.property.1.2
  have firstBounds := _root_.cantorSet_subset_unitInterval firstMember
  have secondBounds := _root_.cantorSet_subset_unitInterval secondMember
  have slope := slopes point.val.1 firstBounds point.val.2 secondBounds
  obtain ⟨⟨first,firstEqual⟩,⟨second,secondEqual⟩⟩ := near_axis_reciprocal_isolated_rational
    n d p q P Q ((1/3 : ℝ)^(n*k+d)) positivePReal positiveResidual
    _ _ _ _ bounds firstGap middleGap point
      (by
        unfold nearAxisHorizontal
        apply div_pos
        · exact_mod_cast (show 0 < n by omega)
        · linarith [firstBounds.1]) slope.2 isolated
  have uPositive : 0 < ((P : ℝ)+point.val.1)/3^p :=
    div_pos (by linarith [firstBounds.1]) (by positivity)
  have vUpper : ((Q : ℝ)+1-point.val.2)/3^q ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < (3 : ℝ)^q)).2
    have castBound : (Q : ℝ)+1 ≤ (3 : ℝ)^q := by exact_mod_cast boundQ
    linarith [secondBounds.1]
  have yPositive : 0 < 1-(1/3 : ℝ)^(n*k+d)*((Q+1-point.val.2)/3^q) := by
    have multiplied := mul_le_mul_of_nonneg_left vUpper
      (show (0 : ℝ) ≤ (1/3 : ℝ)^(n*k+d) by positivity)
    nlinarith
  apply positive_rational_coordinates_not_on_fermat n exponent
    ((1/3 : ℝ)^k*((P+point.val.1)/3^p))
    (1-(1/3 : ℝ)^(n*k+d)*((Q+1-point.val.2)/3^q)) (by positivity) yPositive
  · refine ⟨(1/3 : ℚ)^k*((P+first)/3^p),?_⟩
    push_cast
    rw [firstEqual]
  · refine ⟨1-(1/3 : ℚ)^(n*k+d)*((Q+1-second)/3^q),?_⟩
    push_cast
    rw [secondEqual]
  · exact near_axis_log_zero_fermat n d p q k P Q point.val.1 point.val.2
      uPositive (positiveResidual _ secondBounds) point.property.2

end LambdaCantor.Integer
