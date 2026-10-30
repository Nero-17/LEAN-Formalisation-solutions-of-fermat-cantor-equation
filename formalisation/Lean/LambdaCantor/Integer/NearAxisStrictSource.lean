import LambdaCantor.Integer.NearAxisLog
import LambdaCantor.Classical.GeneralCoverLocal

namespace LambdaCantor.Integer

/-- Full-rectangle strict log ratio bounds supply fixed derivative bounds
for the exact near-axis residual, uniformly for sufficiently small scale. -/
theorem near_axis_ratio_bounds (n d p q : ℕ) (P Q a b : ℝ)
    (positiveN : 0 < n) (positiveP : 0 < P) (positiveQ : 0 < Q)
    (positiveA : 0 < a) (positiveB : 0 < b)
    (lowerRatio : a/Q < (n : ℝ)/(P+1))
    (upperRatio : (n : ℝ)/P < b/(Q+1)) :
    ∃ verticalLower verticalUpper : ℝ,
      0 < verticalLower ∧ a*verticalUpper < (n : ℝ)/(P+1) ∧
      (n : ℝ)/P < b*verticalLower ∧
      ∀ᶠ scale : ℝ in nhds 0,
        ContinuousOn (fun point : ℝ × ℝ => nearAxisLog n d p q P Q scale point.1 point.2)
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∧
        Classical.CoordinateBounds (nearAxisLog n d p q P Q scale)
          ((n : ℝ)/(P+1)) ((n : ℝ)/P) verticalLower verticalUpper ∧
        ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
          0 < nearAxisVertical n q Q scale y ∧
          a < nearAxisHorizontal n P x / nearAxisVertical n q Q scale y ∧
          nearAxisHorizontal n P x / nearAxisVertical n q Q scale y < b := by
  let verticalLower : ℝ := (((n : ℝ)/P)/b+1/(Q+1))/2
  let verticalUpper : ℝ := (1/Q+((n : ℝ)/(P+1))/a)/2
  have positiveNReal : (0 : ℝ) < n := by exact_mod_cast positiveN
  have lowerGap : 1/Q < ((n : ℝ)/(P+1))/a := by
    apply (lt_div_iff₀ positiveA).2
    simpa only [div_mul_eq_mul_div,one_mul] using lowerRatio
  have upperGap : ((n : ℝ)/P)/b < 1/(Q+1) := by
    apply (div_lt_iff₀ positiveB).2
    simpa only [div_mul_eq_mul_div,one_mul] using upperRatio
  have lowerPositive : 0 < verticalLower := by dsimp [verticalLower]; positivity
  have lowerBelow : verticalLower < 1/(Q+1) := by dsimp [verticalLower]; linarith
  have upperAbove : 1/Q < verticalUpper := by dsimp [verticalUpper]; linarith
  have upperPositive : 0 < verticalUpper := lt_trans (by positivity) upperAbove
  have lowerStrong : (n : ℝ)/P < b*verticalLower := by
    have base := (div_lt_iff₀ positiveB).1
      (show ((n : ℝ)/P)/b < verticalLower by dsimp [verticalLower]; linarith)
    nlinarith
  have upperStrong : a*verticalUpper < (n : ℝ)/(P+1) := by
    have base := (lt_div_iff₀ positiveA).1
      (show verticalUpper < ((n : ℝ)/(P+1))/a by dsimp [verticalUpper]; linarith)
    nlinarith
  let error : ℝ := min (1/(Q+1)-verticalLower) (verticalUpper-1/Q)/2
  have errorPositive : 0 < error := by
    dsimp [error]
    exact div_pos (lt_min (sub_pos.mpr lowerBelow) (sub_pos.mpr upperAbove)) (by norm_num)
  have errorLower : error < 1/(Q+1)-verticalLower := by
    have first := min_le_left (1/(Q+1)-verticalLower) (verticalUpper-1/Q)
    dsimp [error]
    linarith
  have errorUpper : error < verticalUpper-1/Q := by
    have second := min_le_right (1/(Q+1)-verticalLower) (verticalUpper-1/Q)
    dsimp [error]
    linarith
  refine ⟨verticalLower,verticalUpper,lowerPositive,upperStrong,lowerStrong,?_⟩
  filter_upwards [nearAxisVertical_uniform n q positiveN Q error positiveQ errorPositive]
    with scale uniform
  have verticalBounds : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      verticalLower ≤ nearAxisVertical n q Q scale y ∧
        nearAxisVertical n q Q scale y ≤ verticalUpper := by
    intro y membership
    have denominatorPositive : 0 < Q+1-y := by linarith [membership.2]
    have baseLower : 1/(Q+1) ≤ 1/(Q+1-y) :=
      div_le_div_of_nonneg_left (by norm_num) denominatorPositive (by linarith [membership.1])
    have baseUpper : 1/(Q+1-y) ≤ 1/Q :=
      div_le_div_of_nonneg_left (by norm_num) positiveQ (by linarith [membership.2])
    have estimate := abs_lt.mp (uniform y membership).2
    constructor <;> linarith
  refine ⟨continuousOn_nearAxisLog n d p q P Q scale positiveP
    (fun y hy => (uniform y hy).1),?_,?_⟩
  · apply Classical.coordinateBounds_of_hasDerivAt
      (nearAxisLog n d p q P Q scale) (fun x _ => nearAxisHorizontal n P x)
      (fun _ y => nearAxisVertical n q Q scale y)
    · intro x hx y hy
      exact hasDerivAt_nearAxisHorizontal n d p q P Q scale x y (by linarith [hx.1])
    · intro x hx y hy
      exact hasDerivAt_nearAxisVertical n d p q P Q scale x y (uniform y hy).1
    · intro x hx y hy
      exact nearAxisHorizontal_bounds n P x positiveP hx
    · intro x hx y hy
      exact verticalBounds y hy
  · intro x hx y hy
    have horizontal := nearAxisHorizontal_bounds n P x positiveP hx
    have vertical := verticalBounds y hy
    have verticalPositive : 0 < nearAxisVertical n q Q scale y := lowerPositive.trans_le vertical.1
    refine ⟨verticalPositive,(lt_div_iff₀ verticalPositive).2 ?_,
      (div_lt_iff₀ verticalPositive).2 ?_⟩
    · have multiplied := mul_le_mul_of_nonneg_left vertical.2 positiveA.le
      nlinarith [horizontal.1]
    · have multiplied := mul_le_mul_of_nonneg_left vertical.1 positiveB.le
      nlinarith [horizontal.2]

theorem near_axis_strict_bounds (n d p q : ℕ) (P Q a b : ℝ)
    (positiveN : 0 < n) (positiveP : 0 < P) (positiveQ : 0 < Q)
    (lowerBand : 1 < a) (upperBand : b < 3) (positiveB : 0 < b)
    (lowerRatio : a/Q < (n : ℝ)/(P+1))
    (upperRatio : (n : ℝ)/P < b/(Q+1)) :
    ∃ verticalLower verticalUpper : ℝ,
      0 < verticalLower ∧ verticalUpper ≤ (n : ℝ)/(P+1) ∧
      (n : ℝ)/P ≤ 3*verticalLower ∧
      ∀ᶠ scale : ℝ in nhds 0,
        ContinuousOn (fun point : ℝ × ℝ => nearAxisLog n d p q P Q scale point.1 point.2)
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∧
        Classical.CoordinateBounds (nearAxisLog n d p q P Q scale)
          ((n : ℝ)/(P+1)) ((n : ℝ)/P) verticalLower verticalUpper ∧
        ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
          0 < nearAxisVertical n q Q scale y ∧
          a < nearAxisHorizontal n P x / nearAxisVertical n q Q scale y ∧
          nearAxisHorizontal n P x / nearAxisVertical n q Q scale y < b := by
  obtain ⟨verticalLower,verticalUpper,positive,first,middle,eventual⟩ :=
    near_axis_ratio_bounds n d p q P Q a b positiveN positiveP positiveQ
      (by linarith) positiveB lowerRatio upperRatio
  have upperPositive : 0 < verticalUpper := by
    have positiveQinv : 0 < 1/Q := by positivity
    have witness := eventual.self_of_nhds
    have bounds := witness.2.1.vertical 0 (by norm_num) 0 (by norm_num) 1 (by norm_num) (by norm_num)
    nlinarith
  exact ⟨verticalLower,verticalUpper,positive,by nlinarith,by nlinarith,eventual⟩

theorem near_axis_cantor_source_eventually (n d p q : ℕ) (P Q a b : ℝ)
    (positiveN : 0 < n) (positiveP : 0 < P) (positiveQ : 0 < Q)
    (lowerBand : 1 < a) (upperBand : b < 3) (positiveB : 0 < b)
    (lowerRatio : a/Q < (n : ℝ)/(P+1))
    (upperRatio : (n : ℝ)/P < b/(Q+1))
    (lowerCorner : nearAxisLog n d p q P Q 0 0 0 < 0)
    (upperCorner : 0 < nearAxisLog n d p q P Q 0 1 1) :
    ∀ᶠ scale : ℝ in nhds 0, ∃ first second : ℝ,
      first ∈ _root_.cantorSet ∧ second ∈ _root_.cantorSet ∧
      nearAxisLog n d p q P Q scale first second = 0 := by
  obtain ⟨verticalLower,verticalUpper,_,firstGap,middleGap,eventual⟩ :=
    near_axis_strict_bounds n d p q P Q a b positiveN positiveP positiveQ
      lowerBand upperBand positiveB lowerRatio upperRatio
  filter_upwards [eventual,nearAxisLog_corners_persist n d p q P Q positiveN positiveQ
    lowerCorner upperCorner] with scale bounds corners
  obtain ⟨first,second,firstMember,secondMember,equation⟩ :=
    Classical.general_cantor_level_local (nearAxisLog n d p q P Q scale) bounds.1
      _ _ _ _ bounds.2.1 firstGap middleGap 0 0 1 0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simpa using corners.1.le) (by simpa using corners.2.le)
  exact ⟨first,second,firstMember,secondMember,by simpa using equation⟩

end LambdaCantor.Integer
