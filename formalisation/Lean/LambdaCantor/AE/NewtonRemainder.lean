import LambdaCantor.AE.CenteredNewtonKernel
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set

namespace LambdaCantor.AE

theorem abs_sub_left_le_of_mem_uIcc {first last point : ℝ} (membership : point ∈ uIcc first last) :
    |point - first| ≤ |last - first| := by
  rcases le_total first last with ordered | ordered
  · rw [uIcc_of_le ordered] at membership
    rw [abs_of_nonneg (sub_nonneg.mpr membership.1), abs_of_nonneg (sub_nonneg.mpr ordered)]
    linarith [membership.2]
  · rw [uIcc_of_ge ordered] at membership
    rw [abs_of_nonpos (sub_nonpos.mpr membership.2), abs_of_nonpos (sub_nonpos.mpr ordered)]
    linarith [membership.1]

/-- First-order Taylor control obtained by two applications of the ordinary
mean value theorem. The constant is deliberately not optimized. -/
theorem first_order_remainder_bound
    (function firstDerivative secondDerivative : ℝ → ℝ) {freezing root bound : ℝ}
    (bound_nonnegative : 0 ≤ bound)
    (first_derivative : ∀ point ∈ uIcc freezing root,
      HasDerivAt function (firstDerivative point) point)
    (second_derivative : ∀ point ∈ uIcc freezing root,
      HasDerivAt firstDerivative (secondDerivative point) point)
    (second_bound : ∀ point ∈ uIcc freezing root, |secondDerivative point| ≤ bound) :
    |function root - function freezing - firstDerivative freezing * (root - freezing)| ≤
      bound * |root - freezing| ^ 2 := by
  have derivative_difference : ∀ point ∈ uIcc freezing root,
      |firstDerivative point - firstDerivative freezing| ≤ bound * |root - freezing| := by
    intro point membership
    have estimate := (convex_uIcc freezing root).norm_image_sub_le_of_norm_deriv_le
      (fun parameter member => (second_derivative parameter member).differentiableAt)
      (fun parameter member => by
        rw [(second_derivative parameter member).deriv]
        simpa only [Real.norm_eq_abs] using second_bound parameter member)
      (left_mem_uIcc) membership
    calc
      |firstDerivative point - firstDerivative freezing| ≤ bound * |point - freezing| := by
        simpa only [Real.norm_eq_abs] using estimate
      _ ≤ bound * |root - freezing| :=
        mul_le_mul_of_nonneg_left (abs_sub_left_le_of_mem_uIcc membership) bound_nonnegative
  have derivative_remainder : ∀ point ∈ uIcc freezing root,
      HasDerivAt (fun parameter => function parameter - function freezing -
        firstDerivative freezing * (parameter - freezing))
        (firstDerivative point - firstDerivative freezing) point := by
    intro point membership
    apply ((((first_derivative point membership).sub_const (function freezing)).sub
      (((hasDerivAt_id point).sub_const freezing).const_mul (firstDerivative freezing))).congr_of_eventuallyEq
        (f₁ := fun parameter : ℝ => function parameter - function freezing -
          firstDerivative freezing * (parameter - freezing))
        (Filter.Eventually.of_forall (fun _ => rfl))).congr_deriv
    simp only [mul_one]
  have estimate := (convex_uIcc freezing root).norm_image_sub_le_of_norm_deriv_le
    (fun parameter member => (derivative_remainder parameter member).differentiableAt)
    (fun parameter member => by
      rw [(derivative_remainder parameter member).deriv]
      simpa only [Real.norm_eq_abs] using derivative_difference parameter member)
    (left_mem_uIcc) (right_mem_uIcc)
  simpa only [sub_self, mul_zero, sub_zero, Real.norm_eq_abs, pow_two, mul_assoc] using estimate

/-- The complete Newton error splits into the frozen tail Taylor error, the
mixed parameter/tail error, and the second parameter derivative error. This
also accounts for the dependence of the same-address tails on the parameter. -/
theorem complete_newton_error_bound
    (actual baseline baselineFirst baselineSecond : ℝ → ℝ)
    {freezing root firstCoefficient secondCoefficient firstTail secondTail
      tailError mixedBound secondBound : ℝ}
    (actual_zero : actual root = 0)
    (slope_nonzero : baselineFirst freezing ≠ 0)
    (second_nonnegative : 0 ≤ secondBound)
    (actual_derivative : ∀ point ∈ uIcc freezing root, DifferentiableAt ℝ actual point)
    (baseline_derivative : ∀ point ∈ uIcc freezing root,
      HasDerivAt baseline (baselineFirst point) point)
    (baseline_second : ∀ point ∈ uIcc freezing root,
      HasDerivAt baselineFirst (baselineSecond point) point)
    (second_bound : ∀ point ∈ uIcc freezing root, |baselineSecond point| ≤ secondBound)
    (mixed_bound : ∀ point ∈ uIcc freezing root,
      |deriv actual point - baselineFirst point| ≤ mixedBound)
    (tail_remainder : |actual freezing - baseline freezing -
      firstCoefficient * firstTail - secondCoefficient * secondTail| ≤ tailError) :
    |root - centeredNewtonValue freezing (baseline freezing) (baselineFirst freezing)
      firstCoefficient secondCoefficient firstTail secondTail| ≤
      (tailError + mixedBound * |root - freezing| + secondBound * |root - freezing| ^ 2) /
        |baselineFirst freezing| := by
  have parameter_remainder := first_order_remainder_bound baseline baselineFirst baselineSecond
    second_nonnegative baseline_derivative baseline_second second_bound
  have mixed_remainder :
      |(actual root - baseline root) - (actual freezing - baseline freezing)| ≤
        mixedBound * |root - freezing| := by
    have estimate := (convex_uIcc freezing root).norm_image_sub_le_of_norm_deriv_le
      (fun parameter member => (actual_derivative parameter member).sub
        (baseline_derivative parameter member).differentiableAt)
      (fun parameter member => by
        rw [deriv_sub (actual_derivative parameter member)
          (baseline_derivative parameter member).differentiableAt,
          (baseline_derivative parameter member).deriv]
        simpa only [Real.norm_eq_abs] using mixed_bound parameter member)
      (left_mem_uIcc) (right_mem_uIcc)
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using estimate
  apply centeredNewton_error_of_residual_remainder slope_nonzero
  have decomposition :
      baseline freezing + baselineFirst freezing * (root - freezing) +
          firstCoefficient * firstTail + secondCoefficient * secondTail =
      -((baseline root - baseline freezing - baselineFirst freezing * (root - freezing)) +
        ((actual root - baseline root) - (actual freezing - baseline freezing)) +
        (actual freezing - baseline freezing - firstCoefficient * firstTail - secondCoefficient * secondTail)) := by
    rw [actual_zero]
    ring
  rw [decomposition, abs_neg]
  apply (abs_add_le _ _).trans
  have first_two := (abs_add_le
    (baseline root - baseline freezing - baselineFirst freezing * (root - freezing))
    ((actual root - baseline root) - (actual freezing - baseline freezing))).trans
      (add_le_add parameter_remainder mixed_remainder)
  linarith

end LambdaCantor.AE
