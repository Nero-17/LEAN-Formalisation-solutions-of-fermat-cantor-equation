import LambdaCantor.Last.AnalyticCoarseThreeGapCounting
import LambdaCantor.Last.AnalyticCoarseCapacityCases
import LambdaCantor.Last.AnalyticCoarsePeriodicIntervals

noncomputable section
namespace LambdaCantor.Last

theorem coarse_three_gap_periodic_exclusion {set : Set ℝ}
    {exponent normalizedHull firstLeft firstRight secondLeft secondRight
      thirdLeft thirdRight arcLeft : ℝ}
    (hexponent : 6 ≤ exponent)
    (hhull_lower : 453 / 1000 < normalizedHull) (hhull_upper : normalizedHull < 1)
    (hfirst : firstRight - firstLeft ≤ (33 / 125) * exponent * normalizedHull)
    (hsecond : secondRight - secondLeft ≤ (113 / 1000) * exponent * normalizedHull)
    (hthird : thirdRight - thirdLeft ≤ (17 / 200) * exponent * normalizedHull)
    (hclassification : ∀ left : ℝ,
      -exponent * normalizedHull ≤ left → left + normalizedHull ≤ 0 →
      (∀ point ∈ set, point ∉ Set.Ioo left (left + normalizedHull)) →
      (firstLeft ≤ left ∧ left + normalizedHull ≤ firstRight) ∨
      (secondLeft ≤ left ∧ left + normalizedHull ≤ secondRight) ∨
      (thirdLeft ≤ left ∧ left + normalizedHull ≤ thirdRight)) :
    ¬ PeriodicSetAvoids set 1 arcLeft (arcLeft + normalizedHull) := by
  intro hempty
  have hhull : 0 < normalizedHull := by linarith
  obtain ⟨indices, hcard, hindices⟩ := coarse_consecutive_integer_arc_family
    (arcLeft := arcLeft) (show 1 ≤ exponent by linarith) hhull.le
  have hcapacity := coarse_three_gap_capacity_of_cover hhull
    hfirst hsecond hthird indices (by
      intro index hindex
      have hbounds := hindices index hindex
      have hcase := hclassification (arcLeft + (index : ℝ)) hbounds.1 (by linarith) (by
        intro point hpoint hinside
        apply hempty point hpoint (-index)
        simp only [Int.cast_neg, mul_one, Set.mem_Ioo]
        constructor <;> linarith [hinside.1, hinside.2])
      rcases hcase with hfirst | hsecond | hthird
      · exact Or.inl ⟨hfirst.1, by linarith [hfirst.2]⟩
      · exact Or.inr (Or.inl ⟨hsecond.1, by linarith [hsecond.2]⟩)
      · exact Or.inr (Or.inr ⟨hthird.1, by linarith [hthird.2]⟩))
  have hstrict := coarse_three_gap_capacity_insufficient hexponent hhull_lower hhull_upper
  omega

end LambdaCantor.Last
