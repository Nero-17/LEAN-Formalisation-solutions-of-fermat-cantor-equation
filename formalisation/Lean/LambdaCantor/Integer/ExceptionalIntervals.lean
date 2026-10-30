import LambdaCantor.Integer.ExceptionalCertificate
import LambdaCantor.Integer.ExceptionalSource
import LambdaCantor.Common
import Mathlib.Tactic.Push

noncomputable section
namespace LambdaCantor.Integer.Exceptional

def rationalIntervalUnion (intervals : List (ℚ × ℚ)) : Set ℝ :=
  {level | ∃ interval ∈ intervals, (interval.1 : ℝ) ≤ level ∧ level ≤ (interval.2 : ℝ)}

theorem scaled_intervals_eq (denominator : ℤ) (positive : 0 < denominator)
    (intervals : List (ℤ × ℤ)) (rationalIntervals : List (ℚ × ℚ))
    (exact_intervals : intervals.map (fun interval =>
      ((interval.1 : ℚ)/denominator,(interval.2 : ℚ)/denominator)) = rationalIntervals) :
    innerTarget denominator intervals = rationalIntervalUnion rationalIntervals := by
  have positive_real : (0:ℝ) < denominator := by exact_mod_cast positive
  ext level
  constructor
  · rintro ⟨interval,membership,lower,upper⟩
    refine ⟨((interval.1 : ℚ)/denominator,(interval.2 : ℚ)/denominator),?_,?_,?_⟩
    · rw [← exact_intervals]
      exact List.mem_map.mpr ⟨interval,membership,rfl⟩
    · push_cast
      apply (div_le_iff₀ positive_real).mpr
      nlinarith
    · push_cast
      apply (le_div_iff₀ positive_real).mpr
      nlinarith
  · rintro ⟨interval,membership,lower,upper⟩
    rw [← exact_intervals] at membership
    obtain ⟨original,original_member,rfl⟩ := List.mem_map.mp membership
    push_cast at lower upper
    refine ⟨original,original_member,?_,?_⟩
    · have cleared := (div_le_iff₀ positive_real).mp lower
      nlinarith
    · have cleared := (le_div_iff₀ positive_real).mp upper
      nlinarith

def switchLevels (slope : ℝ) : Set ℝ :=
  Set.Icc (1/3) ((slope+1)/6) ∪ Set.Icc (slope/3) ((slope+3)/6) ∪
    Set.Icc ((slope+1)/3) ((3*slope+1)/6)

def trimmedSwitchLevels (slope margin : ℝ) : Set ℝ :=
  Set.Icc (1/3+margin) ((slope+1)/6-margin) ∪
    Set.Icc (slope/3+margin) ((slope+3)/6-margin) ∪
    Set.Icc ((slope+1)/3+margin) ((3*slope+1)/6-margin)

theorem rational_switch_intervals (slope : ℚ) :
    rationalIntervalUnion [(1/3,(slope+1)/6),(slope/3,(slope+3)/6),
      ((slope+1)/3,(3*slope+1)/6)] = switchLevels (slope : ℝ) := by
  ext level
  simp [rationalIntervalUnion,switchLevels,or_assoc]

theorem rational_trimmed_switch_intervals (slope margin : ℚ) :
    rationalIntervalUnion [(1/3+margin,(slope+1)/6-margin),(slope/3+margin,(slope+3)/6-margin),
      ((slope+1)/3+margin,(3*slope+1)/6-margin)] = trimmedSwitchLevels slope margin := by
  ext level
  simp [rationalIntervalUnion,trimmedSwitchLevels,or_assoc]

theorem trimmed_switch_robust (slope margin returned value : ℝ)
    (membership : returned ∈ trimmedSwitchLevels slope margin)
    (close : dist value returned < margin) : value ∈ switchLevels slope := by
  rw [Real.dist_eq,abs_lt] at close
  rcases membership with (first | second) | third
  · exact Or.inl (Or.inl ⟨by linarith [first.1],by linarith [first.2]⟩)
  · exact Or.inl (Or.inr ⟨by linarith [second.1],by linarith [second.2]⟩)
  · exact Or.inr ⟨by linarith [third.1],by linarith [third.2]⟩

theorem switch_levels_bounded (slope : ℝ) (positive : 1 < slope) (below : slope < 3)
    (level : ℝ) (membership : level ∈ switchLevels slope) :
    0 ≤ level ∧ level ≤ (slope+1)/2 := by
  rcases membership with (first | second) | third
  · constructor <;> linarith [first.1,first.2]
  · constructor <;> linarith [second.1,second.2]
  · constructor <;> linarith [third.1,third.2]

theorem Source.intercept_mem_switch (source : Source) (valid : source.Valid) :
    (source.intercept : ℝ) ∈ switchLevels source.slope := by
  rcases valid with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,intercept,_⟩
  rcases intercept with first | second | third
  · apply Or.inl; apply Or.inl
    constructor
    · simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        (Rat.cast_le (K := ℝ)).mpr first.1.le
    · exact_mod_cast first.2.le
  · apply Or.inl; apply Or.inr
    constructor
    · exact_mod_cast second.1.le
    · exact_mod_cast second.2.le
  · apply Or.inr
    constructor
    · exact_mod_cast third.1.le
    · exact_mod_cast third.2.le

end LambdaCantor.Integer.Exceptional
