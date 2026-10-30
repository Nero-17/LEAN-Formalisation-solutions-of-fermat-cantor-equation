import LambdaCantor.Last.AnalyticIsolatedOrbit
import LambdaCantor.Last.AnalyticIsolatedTopology
import LambdaCantor.Last.AnalyticIsolatedFilling
import LambdaCantor.Last.AnalyticIsolatedAddressCore

noncomputable section
namespace LambdaCantor.Last

def AffineChildClosed (ratio slope level : ℝ) (digit : Bool × Bool) : Prop :=
  level ∈ Set.Icc (affineChildOffset ratio slope digit)
    (affineChildOffset ratio slope digit+ratio*(1+slope))

theorem affine_exclusive_of_unique_closed {ratio slope level : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2) (slope_lower : 1 ≤ slope)
    (digit : Bool × Bool) (inside : AffineChildClosed ratio slope level digit)
    (unique : ∀ other : Bool × Bool, other ≠ digit → ¬ AffineChildClosed ratio slope level other) :
    AffineExclusiveRegion ratio slope level digit := by
  have reference_order : 0 ≤ (slope-1)*(1-ratio) :=
    mul_nonneg (sub_nonneg.mpr slope_lower) (by linarith)
  rcases digit with ⟨first, second⟩
  cases first <;> cases second
  · change level ≤ 1-ratio
    by_contra failure
    apply unique (true,false) (by decide)
    simp only [AffineChildClosed, affineChildOffset, Set.mem_Icc, if_true,
      Bool.false_eq_true, if_false, mul_zero, zero_add, add_zero, mul_one] at *
    constructor <;> nlinarith
  · change 1+ratio*slope ≤ level ∧ level ≤ (1-ratio)*(1+slope)
    constructor
    · by_contra failure
      apply unique (true,false) (by decide)
      simp only [AffineChildClosed, affineChildOffset, Set.mem_Icc, if_true,
        Bool.false_eq_true, if_false, mul_zero, zero_add, add_zero, mul_one] at *
      constructor <;> nlinarith
    · by_contra failure
      apply unique (true,true) (by decide)
      simp only [AffineChildClosed, affineChildOffset, Set.mem_Icc, if_true,
        Bool.false_eq_true, if_false, mul_zero, zero_add, add_zero, mul_one] at *
      constructor <;> nlinarith
  · change ratio*(1+slope) ≤ level ∧ level ≤ slope*(1-ratio)
    constructor
    · by_contra failure
      apply unique (false,false) (by decide)
      simp only [AffineChildClosed, affineChildOffset, Set.mem_Icc, if_true,
        Bool.false_eq_true, if_false, mul_zero, zero_add, add_zero, mul_one] at *
      constructor <;> nlinarith
    · by_contra failure
      apply unique (false,true) (by decide)
      simp only [AffineChildClosed, affineChildOffset, Set.mem_Icc, if_true,
        Bool.false_eq_true, if_false, mul_zero, zero_add, add_zero, mul_one] at *
      constructor <;> nlinarith
  · change ratio+slope ≤ level
    by_contra failure
    apply unique (false,true) (by decide)
    simp only [AffineChildClosed, affineChildOffset, Set.mem_Icc, if_true,
      Bool.false_eq_true, if_false, mul_zero, zero_add, add_zero, mul_one] at *
    constructor <;> nlinarith

theorem affine_closed_word_hull_filled {ratio slope level : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2)
    (outer : 1-2*ratio < ratio*slope) (middle : (1-2*ratio)*slope < 1)
    (word : List (Bool × Bool))
    (brackets : level ∈ Set.Icc
      (positiveLinearContinuous slope (wordMap ratio word 0))
      (positiveLinearContinuous slope (wordMap ratio word (1,1)))) :
    ∃ point ∈ wordCylinder ratio word, positiveLinearContinuous slope point = level := by
  have growth : CoordinateGrowth (fun point : ℝ × ℝ => point.1+slope*point.2) 1 1 slope slope := by
    simpa using coordinateGrowth_linear_add_lipschitz
      (LipschitzWith.const (0 : ℝ) : LipschitzWith 0 (fun _ : ℝ × ℝ => (0 : ℝ))) slope
  exact nonlinear_word_closed_hull_filled growth (positiveLinearContinuous slope).continuous
    positive less_half (by simpa using outer) middle word brackets

theorem positiveLinear_wordMap (ratio slope : ℝ) (word : List (Bool × Bool)) (point : ℝ × ℝ) :
    positiveLinearContinuous slope (wordMap ratio word point) =
      positiveLinearContinuous slope (wordMap ratio word 0)+ratio^word.length*positiveLinearContinuous slope point := by
  rw [wordMap_affine, map_add, map_smul]
  rfl

theorem affine_closed_child_bounds {ratio slope : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (slope_nonnegative : 0 ≤ slope)
    (digit : Bool × Bool) {tail : ℝ × ℝ} (tail_mem : tail ∈ cantorDust ratio) :
    AffineChildClosed ratio slope (positiveLinearContinuous slope (wordMap ratio [digit] tail)) digit := by
  have first := cantorSet_subset_unitInterval nonnegative less_one tail_mem.1
  have second := cantorSet_subset_unitInterval nonnegative less_one tail_mem.2
  have first_scaled_lower : 0 ≤ ratio*tail.1 := mul_nonneg nonnegative first.1
  have first_scaled_upper : ratio*tail.1 ≤ ratio := by
    nlinarith [mul_nonneg nonnegative (sub_nonneg.mpr first.2)]
  have second_scaled_lower : 0 ≤ ratio*slope*tail.2 :=
    mul_nonneg (mul_nonneg nonnegative slope_nonnegative) second.1
  have second_scaled_upper : ratio*slope*tail.2 ≤ ratio*slope := by
    nlinarith [mul_nonneg (mul_nonneg nonnegative slope_nonnegative) (sub_nonneg.mpr second.2)]
  rcases digit with ⟨firstDigit, secondDigit⟩
  cases firstDigit <;> cases secondDigit <;>
    simp [AffineChildClosed, affineChildOffset, positiveLinearContinuous, positiveLinear, wordMap, digitPoint] <;>
    constructor <;> nlinarith

theorem affine_child_endpoint_values (ratio slope : ℝ) (digit : Bool × Bool) :
    positiveLinearContinuous slope (wordMap ratio [digit] 0) = affineChildOffset ratio slope digit ∧
      positiveLinearContinuous slope (wordMap ratio [digit] (1,1)) =
        affineChildOffset ratio slope digit+ratio*(1+slope) := by
  rcases digit with ⟨first, second⟩
  cases first <;> cases second <;> constructor <;>
    simp [positiveLinearContinuous, positiveLinear, wordMap, digitPoint, affineChildOffset] <;> ring

theorem pairedAddressTail_affine_orbit {ratio : ℝ}
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1) (slope : ℝ)
    (digits : ℕ → Bool × Bool) (depth : ℕ) :
    positiveLinearContinuous slope (pairedAddressTail ratio digits depth) =
      affineChildOffset ratio slope (digits depth)+ratio*
        positiveLinearContinuous slope (pairedAddressTail ratio digits (depth+1)) := by
  rw [pairedAddressTail_recurrence nonnegative less_one digits depth]
  rcases digit_eq : digits depth with ⟨first, second⟩
  cases first <;> cases second <;>
    simp [digit_eq, positiveLinearContinuous, positiveLinear, wordMap, digitPoint, affineChildOffset] <;>
    ring

end LambdaCantor.Last
