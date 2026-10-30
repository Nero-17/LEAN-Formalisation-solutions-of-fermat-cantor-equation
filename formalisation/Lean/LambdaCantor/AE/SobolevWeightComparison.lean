import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

namespace LambdaCantor.AE

/-- The usual inhomogeneous Sobolev weight is controlled by the weight
used in the Fourier energy, for every nonnegative real regularity. -/
theorem sobolev_weight_comparison_standard_le {regularity : ℝ}
    (hregularity : 0 ≤ regularity) (frequency : ℝ) :
    Real.rpow (1 + |frequency| ^ 2) regularity ≤
      Real.rpow (2 : ℝ) regularity *
        (1 + Real.rpow |frequency| (2 * regularity)) := by
  have two_nonnegative : 0 ≤ Real.rpow (2 : ℝ) regularity :=
    Real.rpow_nonneg (by norm_num) regularity
  have power_identity : Real.rpow |frequency| (2 * regularity) =
      Real.rpow (|frequency| ^ 2) regularity :=
    (Real.rpow_mul (abs_nonneg frequency) 2 regularity).trans
      (congrArg (fun value : ℝ => Real.rpow value regularity) (Real.rpow_two |frequency|))
  rcases le_total (|frequency| ^ 2) 1 with square_small | square_large
  · calc
      Real.rpow (1 + |frequency| ^ 2) regularity ≤ Real.rpow (2 : ℝ) regularity :=
        Real.rpow_le_rpow (by linarith [sq_nonneg |frequency|])
          (by linarith) hregularity
      _ ≤ Real.rpow (2 : ℝ) regularity *
          (1 + Real.rpow |frequency| (2 * regularity)) :=
        le_mul_of_one_le_right two_nonnegative
          (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg frequency) (2 * regularity)))
  · calc
      Real.rpow (1 + |frequency| ^ 2) regularity ≤
          Real.rpow (2 * |frequency| ^ 2) regularity :=
        Real.rpow_le_rpow (by linarith [sq_nonneg |frequency|])
          (by linarith) hregularity
      _ = Real.rpow (2 : ℝ) regularity * Real.rpow |frequency| (2 * regularity) :=
        (Real.mul_rpow (x := 2) (y := |frequency| ^ 2) (z := regularity)
          (by norm_num) (sq_nonneg _)).trans
          (congrArg (fun value : ℝ => Real.rpow (2 : ℝ) regularity * value) power_identity.symm)
      _ ≤ Real.rpow (2 : ℝ) regularity *
          (1 + Real.rpow |frequency| (2 * regularity)) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) two_nonnegative

/-- Conversely, the Fourier energy weight is controlled by twice the usual
inhomogeneous Sobolev weight, including zero regularity and zero frequency. -/
theorem sobolev_weight_comparison_implemented_le {regularity : ℝ}
    (hregularity : 0 ≤ regularity) (frequency : ℝ) :
    1 + Real.rpow |frequency| (2 * regularity) ≤
      2 * Real.rpow (1 + |frequency| ^ 2) regularity := by
  have power_identity : Real.rpow |frequency| (2 * regularity) =
      Real.rpow (|frequency| ^ 2) regularity :=
    (Real.rpow_mul (abs_nonneg frequency) 2 regularity).trans
      (congrArg (fun value : ℝ => Real.rpow value regularity) (Real.rpow_two |frequency|))
  have constant_bound : 1 ≤ Real.rpow (1 + |frequency| ^ 2) regularity :=
    Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg |frequency|)) hregularity
  have power_bound : Real.rpow |frequency| (2 * regularity) ≤
      Real.rpow (1 + |frequency| ^ 2) regularity :=
    power_identity.trans_le
      (Real.rpow_le_rpow (sq_nonneg _) (le_add_of_nonneg_left zero_le_one) hregularity)
  exact (add_le_add constant_bound power_bound).trans_eq (two_mul _).symm

#print axioms sobolev_weight_comparison_standard_le
#print axioms sobolev_weight_comparison_implemented_le

end LambdaCantor.AE
