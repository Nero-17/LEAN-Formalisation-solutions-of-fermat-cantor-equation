import LambdaCantor.Last.TwoBandOrbit

noncomputable section
namespace LambdaCantor.Last

def AffineChildInterior (ratio slope level : ℝ) (digit : Bool × Bool) : Prop :=
  level ∈ Set.Ioo (affineChildOffset ratio slope digit)
    (affineChildOffset ratio slope digit + ratio * (1 + slope))

theorem two_band_child_cover {ratio slope level : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (bands : TwoBandSlopes ratio slope) (hlevel : level ∈ Set.Ioo (0 : ℝ) (1 + slope)) :
    ∃ digit : Bool × Bool, AffineChildInterior ratio slope level digit := by
  obtain ⟨hshell, htrapping, hmiddle, houter⟩ := bands.common_inequalities hpositive hhalf
  have hslope : 0 < slope := by linarith [bands.1]
  rcases hlevel with ⟨hlevel_lower, hlevel_upper⟩
  by_cases hfirst : level < ratio * (1 + slope)
  · exact ⟨(false, false), by simpa [AffineChildInterior, affineChildOffset] using ⟨hlevel_lower, hfirst⟩⟩
  · by_cases hsecond : level < 1 + ratio * slope
    · refine ⟨(true, false), ?_⟩
      simp [AffineChildInterior, affineChildOffset]
      constructor <;> nlinarith
    · by_cases hthird : level < ratio + slope
      · refine ⟨(false, true), ?_⟩
        simp [AffineChildInterior, affineChildOffset]
        constructor <;> nlinarith
      · refine ⟨(true, true), ?_⟩
        simp [AffineChildInterior, affineChildOffset]
        constructor <;> nlinarith

theorem affine_exclusive_of_unique_child {ratio slope level : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2) (hslope : 1 < slope)
    (digit : Bool × Bool) (hchild : AffineChildInterior ratio slope level digit)
    (hunique : ∀ other : Bool × Bool, other ≠ digit →
      ¬ AffineChildInterior ratio slope level other) :
    AffineExclusiveRegion ratio slope level digit := by
  have hordering : 0 < (slope - 1) * (1 - ratio) :=
    mul_pos (by linarith) (by linarith)
  rcases digit with ⟨first, second⟩
  cases first <;> cases second
  · change level ≤ 1 - ratio
    by_contra hbound
    apply hunique (true, false) (by decide)
    simp [AffineChildInterior, affineChildOffset, Set.mem_Ioo] at hchild ⊢
    rcases hchild with ⟨hchild_lower, hchild_upper⟩
    constructor <;> nlinarith
  · change 1 + ratio * slope ≤ level ∧ level ≤ (1 - ratio) * (1 + slope)
    constructor
    · by_contra hbound
      apply hunique (true, false) (by decide)
      simp [AffineChildInterior, affineChildOffset, Set.mem_Ioo] at hchild ⊢
      rcases hchild with ⟨hchild_lower, hchild_upper⟩
      constructor <;> nlinarith
    · by_contra hbound
      apply hunique (true, true) (by decide)
      simp [AffineChildInterior, affineChildOffset, Set.mem_Ioo] at hchild ⊢
      rcases hchild with ⟨hchild_lower, hchild_upper⟩
      constructor <;> nlinarith
  · change ratio * (1 + slope) ≤ level ∧ level ≤ slope * (1 - ratio)
    constructor
    · by_contra hbound
      apply hunique (false, false) (by decide)
      simp [AffineChildInterior, affineChildOffset, Set.mem_Ioo] at hchild ⊢
      rcases hchild with ⟨hchild_lower, hchild_upper⟩
      constructor <;> nlinarith
    · by_contra hbound
      apply hunique (false, true) (by decide)
      simp [AffineChildInterior, affineChildOffset, Set.mem_Ioo] at hchild ⊢
      rcases hchild with ⟨hchild_lower, hchild_upper⟩
      constructor <;> nlinarith
  · change ratio + slope ≤ level
    by_contra hbound
    apply hunique (false, true) (by decide)
    simp [AffineChildInterior, affineChildOffset, Set.mem_Ioo] at hchild ⊢
    rcases hchild with ⟨hchild_lower, hchild_upper⟩
    constructor <;> nlinarith

theorem affine_child_return (ratio slope level : ℝ) (digit : Bool × Bool) :
    linearWordReturn ratio (positiveLinear slope) [digit] level =
      (level - affineChildOffset ratio slope digit) / ratio := by
  rcases digit with ⟨first, second⟩
  cases first <;> cases second <;>
    simp [linearWordReturn, returnLevel, wordMap, digitPoint, positiveLinear, affineChildOffset] <;> ring

theorem affine_child_interior_iff {ratio slope level : ℝ} (hpositive : 0 < ratio)
    (digit : Bool × Bool) :
    AffineChildInterior ratio slope level digit ↔
      linearWordReturn ratio (positiveLinear slope) [digit] level ∈ Set.Ioo (0 : ℝ) (1 + slope) := by
  rw [affine_child_return]
  unfold AffineChildInterior
  simp only [Set.mem_Ioo, div_pos_iff_of_pos_right hpositive, div_lt_iff₀ hpositive]
  constructor <;> rintro ⟨hlower, hupper⟩ <;> constructor <;> linarith

/-- Every interior affine level reaches a strict overlap after a finite word.
This is the new two-band statement; it does not use the narrower old criterion. -/
theorem two_band_affine_strict_overlap {ratio slope level : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (bands : TwoBandSlopes ratio slope) (hlevel : level ∈ Set.Ioo (0 : ℝ) (1 + slope)) :
    ∃ word : List (Bool × Bool), ∃ first second : Bool × Bool, first ≠ second ∧
      AffineChildInterior ratio slope
        (linearWordReturn ratio (positiveLinear slope) word level) first ∧
      AffineChildInterior ratio slope
        (linearWordReturn ratio (positiveLinear slope) word level) second := by
  classical
  by_contra hnone
  push_neg at hnone
  let selected : ℝ → Bool × Bool := fun value =>
    if hvalue : value ∈ Set.Ioo (0 : ℝ) (1 + slope) then
      (two_band_child_cover hpositive hhalf bands hvalue).choose else (false, false)
  have hselected : ∀ value ∈ Set.Ioo (0 : ℝ) (1 + slope),
      AffineChildInterior ratio slope value (selected value) := by
    intro value hvalue
    simp only [selected, dif_pos hvalue]
    exact (two_band_child_cover hpositive hhalf bands hvalue).choose_spec
  let run : ℕ → List (Bool × Bool) × ℝ := fun depth =>
    Nat.rec ([], level)
      (fun _ previous => (previous.1 ++ [selected previous.2],
        (previous.2 - affineChildOffset ratio slope (selected previous.2)) / ratio)) depth
  have hrun_zero : run 0 = ([], level) := rfl
  have hrun_succ : ∀ depth, run (depth + 1) =
      ((run depth).1 ++ [selected (run depth).2],
        ((run depth).2 - affineChildOffset ratio slope (selected (run depth).2)) / ratio) := fun _ => rfl
  have hinvariant : ∀ depth,
      (run depth).2 = linearWordReturn ratio (positiveLinear slope) (run depth).1 level ∧
        (run depth).2 ∈ Set.Ioo (0 : ℝ) (1 + slope) := by
    intro depth
    induction depth with
    | zero => exact ⟨by simp [hrun_zero, linearWordReturn, returnLevel, wordMap], hlevel⟩
    | succ depth ih =>
      rw [hrun_succ]
      constructor
      · rw [linearWordReturn_append ratio hpositive.ne', ← ih.1, affine_child_return]
      · simpa only [affine_child_return] using
          (affine_child_interior_iff hpositive _).mp (hselected _ ih.2)
  have hexclusive : ∀ depth, AffineExclusiveRegion ratio slope (run depth).2 (selected (run depth).2) := by
    intro depth
    apply affine_exclusive_of_unique_child hpositive hhalf bands.1 _
      (hselected _ (hinvariant depth).2)
    intro other hdifferent hother
    exact hnone (run depth).1 (selected (run depth).2) other (Ne.symm hdifferent)
      (by simpa [← (hinvariant depth).1] using hselected _ (hinvariant depth).2)
      (by simpa [← (hinvariant depth).1] using hother)
  have hextreme := two_band_exclusive_orbit_extreme hpositive hhalf bands
    (fun depth => (run depth).2) (fun depth => selected (run depth).2)
    (fun depth => ⟨(hinvariant depth).2.1.le, (hinvariant depth).2.2.le⟩) hexclusive
    (fun depth => by rw [hrun_succ]; dsimp; field_simp [hpositive.ne']; ring)
  rcases hextreme with hzero | hone
  · have hzero_level : level = 0 := by simpa [hrun_zero] using hzero
    linarith [hlevel.1]
  · have hone_level : level = 1 + slope := by simpa [hrun_zero] using hone
    linarith [hlevel.2]

end LambdaCantor.Last



