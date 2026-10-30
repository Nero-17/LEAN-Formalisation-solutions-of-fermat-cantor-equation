import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

noncomputable section
namespace LambdaCantor.Last

def PeriodicSetAvoids (set : Set ℝ) (period left right : ℝ) : Prop :=
  ∀ point ∈ set, ∀ shift : ℤ, point + (shift : ℝ) * period ∉ Set.Ioo left right

/-- Normalize an actual empty periodic interval to the negative fundamental
domain. The endpoint zero of the actual set supplies the upper bound. -/
theorem periodic_empty_interval_normalize {set : Set ℝ} {period left right : ℝ}
    (hperiod : 0 < period) (hzero : 0 ∈ set)
    (hempty : PeriodicSetAvoids set period left right) :
    ∃ shift : ℤ,
      -period ≤ left - (shift : ℝ) * period ∧
      right - (shift : ℝ) * period ≤ 0 ∧
      PeriodicSetAvoids set period
        (left - (shift : ℝ) * period) (right - (shift : ℝ) * period) := by
  let shift : ℤ := ⌊left / period⌋ + 1
  have hfloor_lower := (le_div_iff₀ hperiod).mp (Int.floor_le (left / period))
  have hfloor_upper := (div_lt_iff₀ hperiod).mp (Int.lt_floor_add_one (left / period))
  have hshift : (shift : ℝ) = (⌊left / period⌋ : ℤ) + 1 := by simp [shift]
  have hleft_negative : left - (shift : ℝ) * period < 0 := by
    rw [hshift]
    nlinarith
  refine ⟨shift, ?_, ?_, ?_⟩
  · rw [hshift]
    nlinarith
  · by_contra hfailure
    apply hempty 0 hzero shift
    simp only [zero_add, Set.mem_Ioo]
    constructor <;> linarith
  · intro point hpoint translate hinside
    apply hempty point hpoint (translate + shift)
    simp only [Int.cast_add, Set.mem_Ioo]
    constructor <;> nlinarith [hinside.1, hinside.2]

/-- If the hull enlarged by the arc width is longer than one period, an empty
periodic arc has an integer translate wholly inside the hull. -/
theorem periodic_empty_arc_in_hull {set : Set ℝ}
    {period hullLeft width arcLeft : ℝ}
    (hperiod : 0 < period) (hzero : 0 ∈ set) (hendpoint : hullLeft ∈ set)
    (hcover : period < width - hullLeft)
    (hempty : PeriodicSetAvoids set period arcLeft (arcLeft + width)) :
    ∃ shift : ℤ,
      hullLeft ≤ arcLeft - (shift : ℝ) * period ∧
      arcLeft + width - (shift : ℝ) * period ≤ 0 ∧
      PeriodicSetAvoids set period
        (arcLeft - (shift : ℝ) * period)
        (arcLeft + width - (shift : ℝ) * period) := by
  obtain ⟨shift, hlower, hupper, htranslated⟩ :=
    periodic_empty_interval_normalize hperiod hzero hempty
  refine ⟨shift, ?_, hupper, htranslated⟩
  by_contra hfailure
  have hleft : arcLeft - (shift : ℝ) * period < hullLeft := lt_of_not_ge hfailure
  have hright : hullLeft < arcLeft + width - (shift : ℝ) * period := by
    linarith
  apply htranslated hullLeft hendpoint 0
  simpa only [Int.cast_zero, zero_mul, add_zero, Set.mem_Ioo] using And.intro hleft hright

end LambdaCantor.Last
