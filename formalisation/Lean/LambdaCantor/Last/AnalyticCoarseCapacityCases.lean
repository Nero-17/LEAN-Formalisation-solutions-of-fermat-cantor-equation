import LambdaCantor.Last.AnalyticCoarseCapacity

noncomputable section
namespace LambdaCantor.Last

/-- The three explicit logarithmic-gap ratios cannot hold enough translates
of an empty arc. The geometric reduction uses this on 6 ≤ alpha ≤ 20. -/
theorem coarse_three_gap_capacity_insufficient {exponent normalizedHull : ℝ}
    (hexponent : 6 ≤ exponent) (hhull : 453 / 1000 < normalizedHull)
    (hhull_upper : normalizedHull < 1) :
    coarseGapCapacity (33 / 125) exponent normalizedHull +
      coarseGapCapacity (113 / 1000) exponent normalizedHull +
      coarseGapCapacity (17 / 200) exponent normalizedHull <
        ⌊(exponent - 1) * normalizedHull⌋ := by
  let firstCapacity := coarseGapCapacity (33 / 125) exponent normalizedHull
  let secondCapacity := coarseGapCapacity (113 / 1000) exponent normalizedHull
  let thirdCapacity := coarseGapCapacity (17 / 200) exponent normalizedHull
  change firstCapacity + secondCapacity + thirdCapacity < ⌊(exponent - 1) * normalizedHull⌋
  have hhull_nonnegative : 0 ≤ normalizedHull := by linarith
  have hfirst_active : (1 : ℝ) ≤ (33 / 125) * exponent := by nlinarith
  have hfirst_bound : (firstCapacity : ℝ) ≤ ((33 / 125) * exponent - 1) * normalizedHull + 1 :=
    coarseGapCapacity_le_expression hfirst_active
  by_cases htwo : exponent < 1000 / 113
  · have hsecond_zero : secondCapacity = 0 := coarseGapCapacity_inactive (by nlinarith)
    have hthird_zero : thirdCapacity = 0 := coarseGapCapacity_inactive (by nlinarith)
    apply coarse_capacity_linear_contradiction (activeRatioSum := 33 / 125) 1
    · simp only [Int.cast_add, hsecond_zero, hthird_zero, Int.cast_zero, add_zero]
      nlinarith only [hfirst_bound]
    · have hmargin := coarse_capacity_margin_one hexponent hhull.le
      norm_num at hmargin ⊢
      nlinarith only [hmargin]
  · have htwo_lower : 1000 / 113 ≤ exponent := le_of_not_gt htwo
    have hsecond_active : (1 : ℝ) ≤ (113 / 1000) * exponent := by nlinarith
    have hsecond_bound : (secondCapacity : ℝ) ≤
        ((113 / 1000) * exponent - 1) * normalizedHull + 1 :=
      coarseGapCapacity_le_expression hsecond_active
    by_cases hthree : exponent < 200 / 17
    · have hthird_zero : thirdCapacity = 0 := coarseGapCapacity_inactive (by nlinarith)
      by_cases hexponent_large : 91 / 10 ≤ exponent
      · apply coarse_capacity_linear_contradiction (activeRatioSum := 377 / 1000) 2
        · simp only [Int.cast_add, hthird_zero, Int.cast_zero, add_zero]
          nlinarith only [hfirst_bound, hsecond_bound]
        · have hmargin := coarse_capacity_margin_two_exponent hexponent_large hhull.le
          norm_num at hmargin ⊢
          nlinarith only [hmargin]
      · by_cases hhull_large : 47 / 100 ≤ normalizedHull
        · apply coarse_capacity_linear_contradiction (activeRatioSum := 377 / 1000) 2
          · simp only [Int.cast_add, hthird_zero, Int.cast_zero, add_zero]
            nlinarith only [hfirst_bound, hsecond_bound]
          · have hmargin := coarse_capacity_margin_two_hull htwo_lower hhull_large
            norm_num at hmargin ⊢
            nlinarith only [hmargin]
        · have hfirst_one : firstCapacity ≤ 1 := by
            apply coarseGapCapacity_le_nat 1
            have hbound := coarse_product_upper_bound (coefficient := (33 / 125 : ℝ)) (offset := -1)
              (le_of_not_ge hexponent_large) (le_of_not_ge hhull_large)
              (by norm_num) (by norm_num) hhull_nonnegative
            norm_num at hbound ⊢
            nlinarith
          have hsecond_one : secondCapacity ≤ 1 := by
            apply coarseGapCapacity_le_nat 1
            have hbound := coarse_product_upper_bound (coefficient := (113 / 1000 : ℝ)) (offset := -1)
              (le_of_not_ge hexponent_large) (le_of_not_ge hhull_large)
              (by norm_num) (by norm_num) hhull_nonnegative
            norm_num at hbound ⊢
            nlinarith
          have hrequired : (3 : ℤ) ≤ ⌊(exponent - 1) * normalizedHull⌋ := by
            apply Int.le_floor.mpr
            have hbound := coarse_product_lower_bound (coefficient := (1 : ℝ)) (offset := -1)
              htwo_lower hhull.le (by norm_num) (by norm_num) hhull_nonnegative
            norm_num at hbound ⊢
            nlinarith
          omega
    · have hthree_lower : 200 / 17 ≤ exponent := le_of_not_gt hthree
      have hthird_active : (1 : ℝ) ≤ (17 / 200) * exponent := by nlinarith
      have hthird_bound : (thirdCapacity : ℝ) ≤
          ((17 / 200) * exponent - 1) * normalizedHull + 1 :=
        coarseGapCapacity_le_expression hthird_active
      by_cases hexponent_large : 13 ≤ exponent
      · apply coarse_capacity_linear_contradiction (activeRatioSum := 231 / 500) 3
        · simp only [Int.cast_add]
          nlinarith only [hfirst_bound, hsecond_bound, hthird_bound]
        · have hmargin := coarse_capacity_margin_three_exponent hexponent_large hhull.le
          norm_num at hmargin ⊢
          nlinarith only [hmargin]
      · by_cases hhull_large : 49 / 100 ≤ normalizedHull
        · apply coarse_capacity_linear_contradiction (activeRatioSum := 231 / 500) 3
          · simp only [Int.cast_add]
            nlinarith only [hfirst_bound, hsecond_bound, hthird_bound]
          · have hmargin := coarse_capacity_margin_three_hull hthree_lower hhull_large
            norm_num at hmargin ⊢
            nlinarith only [hmargin]
        · have hfirst_two : firstCapacity ≤ 2 := by
            apply coarseGapCapacity_le_nat 2
            have hbound := coarse_product_upper_bound (coefficient := (33 / 125 : ℝ)) (offset := -1)
              (le_of_not_ge hexponent_large) (le_of_not_ge hhull_large)
              (by norm_num) (by norm_num) hhull_nonnegative
            norm_num at hbound ⊢
            nlinarith
          have hsecond_one : secondCapacity ≤ 1 := by
            apply coarseGapCapacity_le_nat 1
            have hbound := coarse_product_upper_bound (coefficient := (113 / 1000 : ℝ)) (offset := -1)
              (le_of_not_ge hexponent_large) (le_of_not_ge hhull_large)
              (by norm_num) (by norm_num) hhull_nonnegative
            norm_num at hbound ⊢
            nlinarith
          have hthird_one : thirdCapacity ≤ 1 := by
            apply coarseGapCapacity_le_nat 1
            have hbound := coarse_product_upper_bound (coefficient := (17 / 200 : ℝ)) (offset := -1)
              (le_of_not_ge hexponent_large) (le_of_not_ge hhull_large)
              (by norm_num) (by norm_num) hhull_nonnegative
            norm_num at hbound ⊢
            nlinarith
          have hrequired_four : (4 : ℤ) ≤ ⌊(exponent - 1) * normalizedHull⌋ := by
            apply Int.le_floor.mpr
            have hbound := coarse_product_lower_bound (coefficient := (1 : ℝ)) (offset := -1)
              hthree_lower hhull.le (by norm_num) (by norm_num) hhull_nonnegative
            norm_num at hbound ⊢
            nlinarith
          by_cases hfirst_one : firstCapacity ≤ 1
          · omega
          · have hfirst_at_least_two : 2 ≤ firstCapacity := by omega
            have hroot_length : 1 ≤ ((33 / 125) * exponent - 1) * normalizedHull :=
              coarseGapCapacity_two_implies_length hfirst_at_least_two
            have hrequired_five : (5 : ℤ) ≤ ⌊(exponent - 1) * normalizedHull⌋ := by
              apply Int.le_floor.mpr
              by_cases hexponent_mid : exponent ≤ 25 / 2
              · have hcomparison : 5 * ((33 / 125) * exponent - 1) ≤ exponent - 1 := by nlinarith
                have hmultiplied := mul_le_mul_of_nonneg_right hcomparison hhull_nonnegative
                norm_num
                nlinarith only [hmultiplied, hroot_length]
              · have hbound := coarse_product_lower_bound (coefficient := (1 : ℝ)) (offset := -1)
                  (le_of_not_ge hexponent_mid) hhull.le (by norm_num) (by norm_num) hhull_nonnegative
                norm_num at hbound ⊢
                nlinarith
            omega

end LambdaCantor.Last
