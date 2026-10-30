import LambdaCantor.Last.ExternalNewhouseBinary
import Mathlib.Tactic.Linarith

noncomputable section
namespace LambdaCantor.Last

/-- A genuine point of the wider set in the interior of the other hull
excludes both complementary-gap containments. This uses actual endpoints. -/
theorem notContainedInGap_pair_of_strict_link
    {first second : Set ℝ} {firstLeft firstRight secondLeft secondRight point : ℝ}
    (hfirst_left : firstLeft ∈ first) (hfirst_right : firstRight ∈ first)
    (hsecond_left : secondLeft ∈ second) (hsecond_right : secondRight ∈ second)
    (hwidth : secondRight - secondLeft ≤ firstRight - firstLeft)
    (hpoint : point ∈ first) (hfirst_bounds : point ∈ Set.Icc firstLeft firstRight)
    (hsecond_strict : point ∈ Set.Ioo secondLeft secondRight) :
    ExternalNewhouse.NotContainedInGap first second ∧
      ExternalNewhouse.NotContainedInGap second first := by
  constructor
  · intro interval hconnected houtside hcontained
    have hleft := hcontained hfirst_left
    have hright := hcontained hfirst_right
    by_cases horder : firstLeft ≤ secondLeft
    · have hendpoint := hconnected.out hleft hright
        (show secondLeft ∈ Set.Icc firstLeft firstRight from
          ⟨horder, by linarith [hsecond_strict.1, hfirst_bounds.2]⟩)
      exact houtside hendpoint hsecond_left
    · have hendpoint := hconnected.out hleft hright
        (show secondRight ∈ Set.Icc firstLeft firstRight from
          ⟨by linarith [hfirst_bounds.1, hsecond_strict.2], by linarith⟩)
      exact houtside hendpoint hsecond_right
  · intro interval hconnected houtside hcontained
    have hpoint_interval := hconnected.out (hcontained hsecond_left) (hcontained hsecond_right)
      (show point ∈ Set.Icc secondLeft secondRight from
        ⟨hsecond_strict.1.le, hsecond_strict.2.le⟩)
    exact houtside hpoint_interval hpoint

end LambdaCantor.Last
