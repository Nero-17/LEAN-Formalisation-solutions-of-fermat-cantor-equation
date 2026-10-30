import LambdaCantor.Last.AnalyticCoarseCapacity
import Mathlib.Data.Int.Interval

noncomputable section
namespace LambdaCantor.Last

theorem coarse_integer_interval_card_le {left right : ℝ} (horder : left ≤ right) :
    ((Finset.Icc ⌈left⌉ ⌊right⌋).card : ℤ) ≤ ⌊right - left⌋ + 1 := by
  have hfloor := Int.floor_mono horder
  have hceil := Int.ceil_le_floor_add_one left
  have hcompatible : ⌈left⌉ ≤ ⌊right⌋ + 1 := by omega
  rw [Int.card_Icc_of_le _ _ hcompatible]
  have hdifference : ⌊right⌋ - ⌈left⌉ ≤ ⌊right - left⌋ := by
    apply Int.le_floor.mpr
    push_cast
    linarith [Int.floor_le right, Int.le_ceil left]
  omega

theorem coarse_finite_integer_card_le {left right : ℝ}
    (indices : Finset ℤ) (horder : left ≤ right)
    (hindices : ∀ index ∈ indices, (index : ℝ) ∈ Set.Icc left right) :
    (indices.card : ℤ) ≤ ⌊right - left⌋ + 1 := by
  have hsubset : indices ⊆ Finset.Icc ⌈left⌉ ⌊right⌋ := by
    intro index hindex
    have hbounds := hindices index hindex
    exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr hbounds.1, Int.le_floor.mpr hbounds.2⟩
  have hcard : (indices.card : ℤ) ≤ ((Finset.Icc ⌈left⌉ ⌊right⌋).card : ℤ) := by
    exact_mod_cast Finset.card_le_card hsubset
  exact hcard.trans (coarse_integer_interval_card_le horder)

theorem coarseGapCapacity_nonnegative {gapRatio exponent normalizedHull : ℝ}
    (hhull : 0 ≤ normalizedHull) :
    0 ≤ coarseGapCapacity gapRatio exponent normalizedHull := by
  by_cases hactive : 1 ≤ gapRatio * exponent
  · rw [coarseGapCapacity, if_pos hactive]
    have hfloor : (0 : ℤ) ≤ ⌊(gapRatio * exponent - 1) * normalizedHull⌋ :=
      Int.le_floor.mpr (by simpa using mul_nonneg (sub_nonneg.mpr hactive) hhull)
    omega
  · simp [coarseGapCapacity, hactive]

/-- Capacity of a genuine gap for a finite collection of integer translates
of an open arc. Inclusion of arc endpoints in the gap closure is sufficient. -/
theorem coarse_gap_capacity_of_actual_translates
    {gapRatio exponent normalizedHull arcLeft gapLeft gapRight : ℝ}
    (hhull : 0 < normalizedHull)
    (hgap : gapRight - gapLeft ≤ gapRatio * exponent * normalizedHull)
    (indices : Finset ℤ)
    (hindices : ∀ index ∈ indices,
      gapLeft ≤ arcLeft + (index : ℝ) ∧
        arcLeft + normalizedHull + (index : ℝ) ≤ gapRight) :
    (indices.card : ℤ) ≤ coarseGapCapacity gapRatio exponent normalizedHull := by
  by_cases hactive : 1 ≤ gapRatio * exponent
  · by_cases hempty : indices = ∅
    · simpa [hempty] using
        coarseGapCapacity_nonnegative (gapRatio := gapRatio) (exponent := exponent) hhull.le
    · obtain ⟨index, hindex⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hbounds := hindices index hindex
      have horder : gapLeft - arcLeft ≤ gapRight - arcLeft - normalizedHull := by
        linarith [hbounds.1, hbounds.2]
      have hcard := coarse_finite_integer_card_le indices horder (by
        intro translate htranslate
        have hbounds := hindices translate htranslate
        constructor <;> linarith [hbounds.1, hbounds.2])
      have hfloor := Int.floor_mono
        (show (gapRight - arcLeft - normalizedHull) - (gapLeft - arcLeft) ≤
          (gapRatio * exponent - 1) * normalizedHull by nlinarith)
      rw [coarseGapCapacity, if_pos hactive]
      omega
  · have hempty : indices = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro index hindex
      have hbounds := hindices index hindex
      have hshort := mul_lt_mul_of_pos_right (lt_of_not_ge hactive) hhull
      nlinarith [hbounds.1, hbounds.2]
    simp [hempty, coarseGapCapacity, hactive]

/-- At least the prescribed number of consecutive translates of an arc fit
inside the actual normalized hull. The upper containment is strict. -/
theorem coarse_consecutive_translates_inside_hull
    {exponent normalizedHull arcLeft : ℝ} (count : ℕ)
    (hcount : (count : ℝ) ≤ (exponent - 1) * normalizedHull) :
    ∃ shift : ℤ, ∀ index : Fin count,
      -exponent * normalizedHull ≤ arcLeft + (shift : ℝ) + (index : ℕ) ∧
        arcLeft + normalizedHull + (shift : ℝ) + (index : ℕ) < 0 := by
  refine ⟨⌈-exponent * normalizedHull - arcLeft⌉, ?_⟩
  intro index
  have hlower := Int.le_ceil (-exponent * normalizedHull - arcLeft)
  have hupper := Int.ceil_lt_add_one (-exponent * normalizedHull - arcLeft)
  have hindex : (index : ℕ) + 1 ≤ count := index.isLt
  have hindex_real : ((index : ℕ) : ℝ) + 1 ≤ (count : ℝ) := by exact_mod_cast hindex
  have hindex_nonnegative : (0 : ℝ) ≤ (index : ℕ) := Nat.cast_nonneg _
  constructor <;> nlinarith

end LambdaCantor.Last
