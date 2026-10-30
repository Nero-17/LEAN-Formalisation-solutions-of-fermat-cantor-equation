import LambdaCantor.SelfSimilarity
import LambdaCantor.First.AddressParameter
import LambdaCantor.ParameterContinuity
import Mathlib.Tactic.Linarith

noncomputable section
namespace LambdaCantor.First.Roots

/-- Attach a fixed binary prefixDigits to an unrestricted complete tail. -/
def cylinderDigits (prefixDigits : ℕ → Bool) (length : ℕ) (tail : ℕ → Bool) : ℕ → Bool :=
  fun index => if index < length then prefixDigits index else tail (index - length)

@[simp] theorem cylinderDigits_after (prefixDigits : ℕ → Bool) (length : ℕ)
    (tail : ℕ → Bool) (index : ℕ) :
    cylinderDigits prefixDigits length tail (length + index) = tail index := by
  simp [cylinderDigits, show ¬length + index < length by omega]

theorem continuous_cylinderDigits (prefixDigits : ℕ → Bool) (length : ℕ) :
    Continuous (cylinderDigits prefixDigits length) := by
  apply continuous_pi
  intro index
  by_cases before : index < length
  · simpa only [cylinderDigits, if_pos before] using
      (continuous_const : Continuous (fun _ : ℕ → Bool => prefixDigits index))
  · simpa only [cylinderDigits, if_neg before] using
      (continuous_apply (index - length) : Continuous (fun tail : ℕ → Bool => tail (index - length)))

/-- These complete addresses represent the actual cylinder coordinates in the source. -/
theorem cylinder_address {ratio : ℝ} (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (prefixDigits : ℕ → Bool) (length : ℕ) (tail : ℕ → Bool) :
    address ratio (cylinderDigits prefixDigits length tail) =
      prefixValue ratio prefixDigits length + ratio ^ length * address ratio tail := by
  rw [address_prefix_tail nonnegative less_one (cylinderDigits prefixDigits length tail) length]
  have prefix_identity : prefixValue ratio (cylinderDigits prefixDigits length tail) length =
      prefixValue ratio prefixDigits length := by
    unfold prefixValue
    congr 1
    apply Finset.sum_congr rfl
    intro index before
    simp [cylinderDigits, Finset.mem_range.mp before]
  rw [prefix_identity]
  have tail_identity : (fun index => cylinderDigits prefixDigits length tail (index + length)) = tail := by
    funext index
    simpa [Nat.add_comm] using cylinderDigits_after prefixDigits length tail index
  rw [tail_identity]

/-- On the positive power curve the ratio of coordinates determines the point.
This is the injectivity part of the state recovery in the root-fibres proof. -/
theorem positive_arc_ratio_injective {exponent x y otherX otherY : ℝ}
    (exponent_pos : 0 < exponent) (x_pos : 0 < x) (y_pos : 0 < y)
    (otherX_pos : 0 < otherX) (otherY_pos : 0 < otherY)
    (curve : x ^ exponent + y ^ exponent = 1)
    (other_curve : otherX ^ exponent + otherY ^ exponent = 1)
    (same_ratio : x / y = otherX / otherY) : x = otherX ∧ y = otherY := by
  have cross : x * otherY = otherX * y :=
    (div_eq_div_iff y_pos.ne' otherY_pos.ne').mp same_ratio
  have equal_y : y = otherY := by
    rcases lt_trichotomy y otherY with less | equal | greater
    · have x_less : x < otherX := by
        by_contra not_less
        have product_nonnegative := mul_nonneg
          (sub_nonneg.mpr (le_of_not_gt not_less)) otherY_pos.le
        nlinarith [mul_pos otherX_pos (sub_pos.mpr less)]
      have := Real.rpow_lt_rpow x_pos.le x_less exponent_pos
      have := Real.rpow_lt_rpow y_pos.le less exponent_pos
      linarith
    · exact equal
    · have otherX_less : otherX < x := by
        by_contra not_less
        have product_nonnegative := mul_nonneg
          (sub_nonneg.mpr (le_of_not_gt not_less)) y_pos.le
        nlinarith [mul_pos x_pos (sub_pos.mpr greater)]
      have := Real.rpow_lt_rpow otherX_pos.le otherX_less exponent_pos
      have := Real.rpow_lt_rpow otherY_pos.le greater exponent_pos
      linarith
  constructor
  · rw [equal_y] at same_ratio
    exact (div_left_inj' otherY_pos.ne').mp same_ratio
  · exact equal_y

/-- The linear-model slope, with the cylinder scale factor fixed, determines a
positive power-curve point. -/
theorem positive_arc_state_injective {exponent scale x y otherX otherY : ℝ}
    (exponent_gt : 1 < exponent) (scale_ne : scale ≠ 0)
    (x_pos : 0 < x) (y_pos : 0 < y) (otherX_pos : 0 < otherX)
    (otherY_pos : 0 < otherY)
    (curve : x ^ exponent + y ^ exponent = 1)
    (other_curve : otherX ^ exponent + otherY ^ exponent = 1)
    (same_state : scale * (x / y) ^ (exponent - 1) =
      scale * (otherX / otherY) ^ (exponent - 1)) :
    x = otherX ∧ y = otherY := by
  apply positive_arc_ratio_injective (by linarith) x_pos y_pos otherX_pos otherY_pos
    curve other_curve
  exact (Real.rpow_left_inj (div_pos x_pos y_pos).le
    (div_pos otherX_pos otherY_pos).le (by linarith)).mp
    (mul_left_cancel₀ scale_ne same_state)

/-- Strong separation survives evaluation at two different root parameters.
The second term is the actual incidence coordinate, rather than a frozen address.
The parameter Lipschitz estimate is displayed explicitly. -/
theorem incidence_separation {lower upper firstRatio secondRatio constant : ℝ}
    (lower_pos : 0 < lower) (upper_lt : upper < 1 / 2)
    (first_mem : firstRatio ∈ Set.Icc lower upper)
    (left right : ℕ → Bool) (depth : ℕ)
    (agreement : ∀ j < depth, left j = right j)
    (different : left depth ≠ right depth)
    (parameter_bound : |address firstRatio right - address secondRatio right| ≤
      constant * |firstRatio - secondRatio|) :
    (1 - 2 * upper) * lower ^ depth ≤
      |address firstRatio left - address secondRatio right| +
        constant * |firstRatio - secondRatio| := by
  have first_pos : 0 < firstRatio := lower_pos.trans_le first_mem.1
  have first_lt : firstRatio < 1 / 2 := first_mem.2.trans_lt upper_lt
  have gap := prefix_separation first_pos first_lt left right depth agreement different
  have power_bound : lower ^ depth ≤ firstRatio ^ depth :=
    pow_le_pow_left₀ lower_pos.le first_mem.1 depth
  have uniform_gap : (1 - 2 * upper) * lower ^ depth ≤
      (1 - 2 * firstRatio) * firstRatio ^ depth := by
    apply mul_le_mul (by linarith [first_mem.2]) power_bound
      (pow_nonneg lower_pos.le _) (by linarith)
  have triangle : |address firstRatio left - address firstRatio right| ≤
      |address firstRatio left - address secondRatio right| +
        |address firstRatio right - address secondRatio right| := by
    simpa [abs_sub_comm] using abs_sub_le (address firstRatio left)
      (address secondRatio right) (address firstRatio right)
  linarith

/-- Uniform incidence separation for actual Cantor addresses: the parameter
movement bound is discharged by differentiating the address series. -/
theorem incidence_separation_uniform {lower upper firstRatio secondRatio : ℝ}
    (lower_pos : 0 < lower) (upper_lt : upper < 1 / 2)
    (first_mem : firstRatio ∈ Set.Icc lower upper)
    (second_mem : secondRatio ∈ Set.Icc lower upper)
    (left right : ℕ → Bool) (depth : ℕ)
    (agreement : ∀ j < depth, left j = right j)
    (different : left depth ≠ right depth) :
    (1 - 2 * upper) * lower ^ depth ≤
      |address firstRatio left - address secondRatio right| +
        addressParameterDerivativeBound upper * |firstRatio - secondRatio| := by
  apply incidence_separation lower_pos upper_lt first_mem left right depth agreement different
  exact address_parameter_lipschitz_estimate lower_pos (by linarith)
    second_mem first_mem right

/-- An incidence neighbourhood of the separation scale fixes the whole prefixDigits.
This is the geometric containment needed to convert prefixDigits masses to a Frostman bound. -/
theorem close_incidence_same_prefix {lower upper firstRatio secondRatio : ℝ}
    (lower_pos : 0 < lower) (upper_lt : upper < 1 / 2)
    (first_mem : firstRatio ∈ Set.Icc lower upper)
    (second_mem : secondRatio ∈ Set.Icc lower upper)
    (left right : ℕ → Bool) (depth : ℕ)
    (close : |address firstRatio left - address secondRatio right| +
      addressParameterDerivativeBound upper * |firstRatio - secondRatio| <
        (1 - 2 * upper) * lower ^ depth) :
    ∀ j < depth, left j = right j := by
  classical
  intro j j_lt
  by_contra different
  have exists_difference : ∃ k, left k ≠ right k := ⟨j, different⟩
  have first_le : Nat.find exists_difference ≤ j := Nat.find_min' exists_difference different
  have separation := incidence_separation_uniform lower_pos upper_lt first_mem second_mem
    left right (Nat.find exists_difference)
    (fun k hk => not_ne_iff.mp (Nat.find_min exists_difference hk))
    (Nat.find_spec exists_difference)
  have lower_lt_one : lower < 1 := by linarith [first_mem.1, first_mem.2]
  have power_bound : lower ^ depth ≤ lower ^ Nat.find exists_difference :=
    pow_le_pow_of_le_one lower_pos.le lower_lt_one.le (by omega)
  have multiplied := mul_le_mul_of_nonneg_left power_bound
    (show 0 ≤ 1 - 2 * upper by linarith)
  linarith

end LambdaCantor.First.Roots
