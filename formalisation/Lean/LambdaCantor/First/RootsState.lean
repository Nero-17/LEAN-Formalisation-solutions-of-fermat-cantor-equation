import LambdaCantor.First.RootsIncidence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor.First.Roots

private theorem ordered_ratio_separation {lower x y otherX otherY : ℝ}
    (lower_pos : 0 < lower) (x_lower : lower ≤ x) (y_lower : lower ≤ y)
    (otherY_lower : lower ≤ otherY) (y_upper : y ≤ 1) (otherY_upper : otherY ≤ 1)
    (x_order : x ≤ otherX) (y_order : otherY ≤ y) :
    lower * (|x - otherX| + |y - otherY|) ≤ |x / y - otherX / otherY| := by
  have y_pos : 0 < y := lower_pos.trans_le y_lower
  have otherY_pos : 0 < otherY := lower_pos.trans_le otherY_lower
  have ratio_order : x / y ≤ otherX / otherY := by
    apply (div_le_div_iff₀ y_pos otherY_pos).2
    calc
      x * otherY ≤ x * y := mul_le_mul_of_nonneg_left y_order (lower_pos.le.trans x_lower)
      _ ≤ otherX * y := mul_le_mul_of_nonneg_right x_order y_pos.le
  have identity : otherX * y - x * otherY =
      (y * otherY) * (otherX / otherY - x / y) := by
    field_simp [y_pos.ne', otherY_pos.ne'] <;> ring
  have product_upper : y * otherY ≤ 1 := by
    calc
      y * otherY ≤ 1 * 1 := mul_le_mul y_upper otherY_upper otherY_pos.le (by norm_num)
      _ = 1 := by ring
  rw [abs_of_nonpos (sub_nonpos.mpr x_order), abs_of_nonneg (sub_nonneg.mpr y_order),
    abs_of_nonpos (sub_nonpos.mpr ratio_order)]
  calc
    _ ≤ y * (otherX - x) + x * (y - otherY) := by
      have first := mul_le_mul_of_nonneg_right y_lower (sub_nonneg.mpr x_order)
      have second := mul_le_mul_of_nonneg_right x_lower (sub_nonneg.mpr y_order)
      nlinarith
    _ = otherX * y - x * otherY := by ring
    _ = (y * otherY) * (otherX / otherY - x / y) := identity
    _ ≤ 1 * (otherX / otherY - x / y) :=
      mul_le_mul_of_nonneg_right product_upper (sub_nonneg.mpr ratio_order)
    _ = _ := by ring

/-- Quantitative recovery of a positive power-curve point from its coordinate
ratio. This is a direct inverse-Lipschitz bound on every positive compact patch,
not just compactness or qualitative injectivity of the state map. -/
theorem positive_arc_ratio_inverse_bound {exponent lower x y otherX otherY : ℝ}
    (exponent_pos : 0 < exponent) (lower_pos : 0 < lower)
    (x_band : x ∈ Set.Icc lower 1) (y_band : y ∈ Set.Icc lower 1)
    (otherX_band : otherX ∈ Set.Icc lower 1) (otherY_band : otherY ∈ Set.Icc lower 1)
    (curve : x ^ exponent + y ^ exponent = 1)
    (other_curve : otherX ^ exponent + otherY ^ exponent = 1) :
    lower * (|x - otherX| + |y - otherY|) ≤ |x / y - otherX / otherY| := by
  have opposite_order : ∀ {firstX firstY secondX secondY : ℝ},
      0 < firstX → 0 < firstY →
      firstX ^ exponent + firstY ^ exponent = 1 →
      secondX ^ exponent + secondY ^ exponent = 1 →
      firstX ≤ secondX → secondY ≤ firstY := by
    intro firstX firstY secondX secondY firstX_pos firstY_pos first_curve second_curve x_order
    by_contra not_le
    have y_order := lt_of_not_ge not_le
    have x_power := Real.rpow_le_rpow firstX_pos.le x_order exponent_pos.le
    have y_power := Real.rpow_lt_rpow firstY_pos.le y_order exponent_pos
    linarith
  rcases le_total x otherX with x_order | x_order
  · exact ordered_ratio_separation lower_pos x_band.1 y_band.1 otherY_band.1
      y_band.2 otherY_band.2 x_order
      (opposite_order (lower_pos.trans_le x_band.1) (lower_pos.trans_le y_band.1)
        curve other_curve x_order)
  · have bound := ordered_ratio_separation lower_pos otherX_band.1 otherY_band.1 y_band.1
      otherY_band.2 y_band.2 x_order
      (opposite_order (lower_pos.trans_le otherX_band.1) (lower_pos.trans_le otherY_band.1)
        other_curve curve x_order)
    simpa only [abs_sub_comm] using bound

end LambdaCantor.First.Roots
