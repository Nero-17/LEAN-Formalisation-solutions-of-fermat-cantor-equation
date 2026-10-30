import LambdaCantor.Integer.NearAxisDifferentiable
import LambdaCantor.Integer.NearAxisEquation
import LambdaCantor.Integer.ExternalFermat
import LambdaCantor.Classical.GoodSlopeIsolation

namespace LambdaCantor.Integer

theorem near_axis_isolated_coordinates_rational (n d p q : ℕ) (P Q scale : ℝ)
    (positiveP : 0 < P)
    (positiveResidual : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < ((Q+1-y)/3^q)*fermatQuotient n (scale*((Q+1-y)/3^q)))
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : Classical.CoordinateBounds (nearAxisLog n d p q P Q scale)
      horizontalLower horizontalUpper verticalLower verticalUpper)
    (firstGap : verticalUpper ≤ horizontalLower) (middleGap : horizontalUpper ≤ 3*verticalLower)
    (point : Classical.cantorLevel (nearAxisLog n d p q P Q scale) 0)
    (verticalPositive : 0 < nearAxisVertical n q Q scale point.val.2)
    (good : GoodSlope (nearAxisHorizontal n P point.val.1/nearAxisVertical n q Q scale point.val.2))
    (isolated : IsOpen ({point} : Set (Classical.cantorLevel (nearAxisLog n d p q P Q scale) 0))) :
    (∃ first : ℚ, (first : ℝ)=point.val.1) ∧
      (∃ second : ℚ, (second : ℝ)=point.val.2) := by
  obtain ⟨first,firstValue⟩ := point.property.1.1
  obtain ⟨second,secondValue⟩ := point.property.1.2
  have firstMember : point.val.1 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]
    exact ⟨first,firstValue⟩
  have secondMember : point.val.2 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]
    exact ⟨second,secondValue⟩
  have firstBounds := _root_.cantorSet_subset_unitInterval firstMember
  have secondBounds := _root_.cantorSet_subset_unitInterval secondMember
  obtain ⟨derivative,differentiable,formula⟩ := nearAxisLog_hasFDerivAt n d p q P Q scale
    point.val.1 point.val.2 (by linarith [firstBounds.1]) (positiveResidual _ secondBounds)
  obtain ⟨radius,radiusPositive,ball⟩ := Metric.isOpen_iff.mp isolated point (by simp)
  have pointEquation : (address (1/3) first,address (1/3) second)=point.val :=
    Prod.ext firstValue secondValue
  have isolatedBall : ∀ other ∈ Classical.cantorLevel (nearAxisLog n d p q P Q scale)
      (nearAxisLog n d p q P Q scale (address (1/3) first) (address (1/3) second)),
      dist other (address (1/3) first,address (1/3) second) < radius →
        other = (address (1/3) first,address (1/3) second) := by
    intro other membership close
    have otherMember : other ∈ Classical.cantorLevel (nearAxisLog n d p q P Q scale) 0 := by
      simpa only [firstValue,secondValue,
        show nearAxisLog n d p q P Q scale point.val.1 point.val.2 = 0 from point.property.2]
        using membership
    have nearby : (⟨other,otherMember⟩ : Classical.cantorLevel (nearAxisLog n d p q P Q scale) 0)
        ∈ Metric.ball point radius := by
      change dist other point.val < radius
      simpa only [pointEquation] using close
    have equality := congrArg Subtype.val (Set.mem_singleton_iff.mp (ball nearby))
    exact equality.trans pointEquation.symm
  have rational := Classical.good_slope_isolated_coordinates_rational
    (nearAxisLog n d p q P Q scale)
    (continuousOn_nearAxisLog n d p q P Q scale positiveP positiveResidual)
    _ _ _ _ bounds firstGap middleGap first second
    (nearAxisHorizontal n P point.val.1) (nearAxisVertical n q Q scale point.val.2)
    verticalPositive good derivative
    (by simpa only [pointEquation] using differentiable) formula radius radiusPositive isolatedBall
  obtain ⟨⟨rationalFirst,firstEqual⟩,⟨rationalSecond,secondEqual⟩⟩ := rational
  exact ⟨⟨rationalFirst,firstEqual.trans firstValue⟩,⟨rationalSecond,secondEqual.trans secondValue⟩⟩

/-- Fermat's theorem excludes every isolated point of this exact normalized
Cantor fibre, after the coordinate-rationality conclusion has been proved. -/
theorem near_axis_no_isolated (n d p q k P Q : ℕ) (exponent : 3 ≤ n)
    (positiveP : 0 < P) (positiveQ : 0 < Q) (boundQ : Q+1 ≤ 3^q)
    (small : (1/3 : ℝ)^(n*k+d) < 1)
    (positiveResidual : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < ((Q+1-y)/3^q)*fermatQuotient n ((1/3 : ℝ)^(n*k+d)*((Q+1-y)/3^q)))
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : Classical.CoordinateBounds (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d)))
      horizontalLower horizontalUpper verticalLower verticalUpper)
    (firstGap : verticalUpper ≤ horizontalLower) (middleGap : horizontalUpper ≤ 3*verticalLower)
    (slopes : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < nearAxisVertical n q Q ((1/3 : ℝ)^(n*k+d)) y ∧
      GoodSlope (nearAxisHorizontal n P x/nearAxisVertical n q Q ((1/3 : ℝ)^(n*k+d)) y)) :
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
  obtain ⟨⟨first,firstEqual⟩,⟨second,secondEqual⟩⟩ := near_axis_isolated_coordinates_rational
    n d p q P Q ((1/3 : ℝ)^(n*k+d)) positivePReal positiveResidual
    _ _ _ _ bounds firstGap middleGap point slope.1 slope.2 isolated
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
