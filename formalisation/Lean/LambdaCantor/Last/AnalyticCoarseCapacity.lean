import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

noncomputable section
namespace LambdaCantor.Last

/-- Upper capacity of a gap whose length divided by the logarithmic hull
length is at most `gapRatio`. -/
def coarseGapCapacity (gapRatio exponent normalizedHull : ℝ) : ℤ :=
  if 1 ≤ gapRatio * exponent then
    ⌊(gapRatio * exponent - 1) * normalizedHull⌋ + 1 else 0

theorem coarseGapCapacity_inactive {gapRatio exponent normalizedHull : ℝ}
    (hinactive : gapRatio * exponent < 1) :
    coarseGapCapacity gapRatio exponent normalizedHull = 0 := by
  simp [coarseGapCapacity, not_le.mpr hinactive]

theorem coarseGapCapacity_le_expression {gapRatio exponent normalizedHull : ℝ}
    (hactive : 1 ≤ gapRatio * exponent) :
    (coarseGapCapacity gapRatio exponent normalizedHull : ℝ) ≤
      (gapRatio * exponent - 1) * normalizedHull + 1 := by
  simp only [coarseGapCapacity, if_pos hactive, Int.cast_add, Int.cast_one]
  exact add_le_add (Int.floor_le ((gapRatio * exponent - 1) * normalizedHull)) (le_refl (1 : ℝ))

theorem coarseGapCapacity_le_nat {gapRatio exponent normalizedHull : ℝ} (bound : ℕ)
    (hbound : (gapRatio * exponent - 1) * normalizedHull < (bound : ℝ)) :
    coarseGapCapacity gapRatio exponent normalizedHull ≤ (bound : ℤ) := by
  by_cases hactive : 1 ≤ gapRatio * exponent
  · simp only [coarseGapCapacity, if_pos hactive]
    have hfloor : ⌊(gapRatio * exponent - 1) * normalizedHull⌋ < (bound : ℤ) :=
      Int.floor_lt.mpr (by exact_mod_cast hbound)
    omega
  · simp [coarseGapCapacity, hactive]

theorem coarseGapCapacity_two_implies_length {gapRatio exponent normalizedHull : ℝ}
    (hcapacity : 2 ≤ coarseGapCapacity gapRatio exponent normalizedHull) :
    1 ≤ (gapRatio * exponent - 1) * normalizedHull := by
  by_cases hactive : 1 ≤ gapRatio * exponent
  · simp only [coarseGapCapacity, if_pos hactive] at hcapacity
    have hfloor : (1 : ℤ) ≤ ⌊(gapRatio * exponent - 1) * normalizedHull⌋ := by omega
    exact_mod_cast Int.le_floor.mp hfloor
  · simp [coarseGapCapacity, hactive] at hcapacity

theorem coarse_product_lower_bound {exponent normalizedHull lowerExponent lowerHull coefficient offset : ℝ}
    (hexponent : lowerExponent ≤ exponent) (hhull : lowerHull ≤ normalizedHull)
    (hcoefficient : 0 ≤ coefficient) (hlower : 0 ≤ coefficient * lowerExponent + offset)
    (hnormalized : 0 ≤ normalizedHull) :
    (coefficient * lowerExponent + offset) * lowerHull ≤
      (coefficient * exponent + offset) * normalizedHull := by
  calc
    _ ≤ (coefficient * lowerExponent + offset) * normalizedHull :=
      mul_le_mul_of_nonneg_left hhull hlower
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_left hexponent hcoefficient) (le_refl offset)) hnormalized

theorem coarse_product_upper_bound {exponent normalizedHull upperExponent upperHull coefficient offset : ℝ}
    (hexponent : exponent ≤ upperExponent) (hhull : normalizedHull ≤ upperHull)
    (hcoefficient : 0 ≤ coefficient) (hupper : 0 ≤ coefficient * upperExponent + offset)
    (hnormalized : 0 ≤ normalizedHull) :
    (coefficient * exponent + offset) * normalizedHull ≤
      (coefficient * upperExponent + offset) * upperHull := by
  calc
    _ ≤ (coefficient * upperExponent + offset) * normalizedHull :=
      mul_le_mul_of_nonneg_right
        (add_le_add (mul_le_mul_of_nonneg_left hexponent hcoefficient) (le_refl offset)) hnormalized
    _ ≤ _ := mul_le_mul_of_nonneg_left hhull hupper

theorem coarse_capacity_linear_contradiction {exponent normalizedHull activeRatioSum : ℝ}
    (activeCount : ℕ) (capacity : ℤ)
    (hcapacity : (capacity : ℝ) ≤ exponent * normalizedHull * activeRatioSum -
      (activeCount : ℝ) * normalizedHull + activeCount)
    (hmargin : (activeCount : ℝ) + 1 <
      (exponent * (1 - activeRatioSum) + activeCount - 1) * normalizedHull) :
    capacity < ⌊(exponent - 1) * normalizedHull⌋ := by
  have hrequired := Int.sub_one_lt_floor ((exponent - 1) * normalizedHull)
  have hreal : (capacity : ℝ) < (⌊(exponent - 1) * normalizedHull⌋ : ℤ) := by
    nlinarith only [hcapacity, hmargin, hrequired]
  exact_mod_cast hreal

theorem coarse_capacity_margin_one {exponent normalizedHull : ℝ}
    (hexponent : 6 ≤ exponent) (hhull : 453 / 1000 ≤ normalizedHull) :
    2 < (exponent * (1 - 33 / 125)) * normalizedHull := by
  have hbound := coarse_product_lower_bound (coefficient := (1 - 33 / 125 : ℝ)) (offset := 0)
    hexponent hhull (by norm_num) (by norm_num) (by linarith)
  norm_num at hbound ⊢
  nlinarith

theorem coarse_capacity_margin_two_exponent {exponent normalizedHull : ℝ}
    (hexponent : 91 / 10 ≤ exponent) (hhull : 453 / 1000 ≤ normalizedHull) :
    3 < (exponent * (1 - 377 / 1000) + 1) * normalizedHull := by
  have hbound := coarse_product_lower_bound (coefficient := (1 - 377 / 1000 : ℝ)) (offset := 1)
    hexponent hhull (by norm_num) (by norm_num) (by linarith)
  norm_num at hbound ⊢
  nlinarith

theorem coarse_capacity_margin_two_hull {exponent normalizedHull : ℝ}
    (hexponent : 1000 / 113 ≤ exponent) (hhull : 47 / 100 ≤ normalizedHull) :
    3 < (exponent * (1 - 377 / 1000) + 1) * normalizedHull := by
  have hbound := coarse_product_lower_bound (coefficient := (1 - 377 / 1000 : ℝ)) (offset := 1)
    hexponent hhull (by norm_num) (by norm_num) (by linarith)
  norm_num at hbound ⊢
  nlinarith

theorem coarse_capacity_margin_three_exponent {exponent normalizedHull : ℝ}
    (hexponent : 13 ≤ exponent) (hhull : 453 / 1000 ≤ normalizedHull) :
    4 < (exponent * (1 - 231 / 500) + 2) * normalizedHull := by
  have hbound := coarse_product_lower_bound (coefficient := (1 - 231 / 500 : ℝ)) (offset := 2)
    hexponent hhull (by norm_num) (by norm_num) (by linarith)
  norm_num at hbound ⊢
  nlinarith

theorem coarse_capacity_margin_three_hull {exponent normalizedHull : ℝ}
    (hexponent : 200 / 17 ≤ exponent) (hhull : 49 / 100 ≤ normalizedHull) :
    4 < (exponent * (1 - 231 / 500) + 2) * normalizedHull := by
  have hbound := coarse_product_lower_bound (coefficient := (1 - 231 / 500 : ℝ)) (offset := 2)
    hexponent hhull (by norm_num) (by norm_num) (by linarith)
  norm_num at hbound ⊢
  nlinarith

end LambdaCantor.Last
