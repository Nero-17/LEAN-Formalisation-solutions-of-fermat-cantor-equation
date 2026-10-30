import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
namespace LambdaCantor.Last

/-- Normalized actual source on a fixed cylinder rectangle, with the second
coordinate reflected to make both partial derivatives positive. -/
def normalizedCylinderSource (exponent coefficient scale firstLeft firstScale secondRight secondScale : ℝ)
    (point : ℝ × ℝ) : ℝ :=
  (firstLeft+firstScale*point.1)^exponent +
    coefficient/(exponent*scale)*((1-scale*secondRight+scale*secondScale*point.2)^exponent-1)

theorem normalizedCylinderSource_continuous {exponent : ℝ} (exponent_ge_one : 1 ≤ exponent)
    (coefficient scale firstLeft firstScale secondRight secondScale : ℝ) :
    Continuous (normalizedCylinderSource exponent coefficient scale firstLeft firstScale secondRight secondScale) := by
  apply Continuous.add
  · exact (continuous_const.add (continuous_const.mul continuous_fst)).rpow_const
      (fun _ => Or.inr (by linarith))
  · exact continuous_const.mul (((continuous_const.add (continuous_const.mul continuous_snd)).rpow_const
      (fun _ => Or.inr (by linarith))).sub continuous_const)

/-- Exact strict derivative of the normalized actual cylinder source. -/
theorem normalizedCylinderSource_hasStrictFDerivAt {exponent scale : ℝ}
    (exponent_ge_one : 1 ≤ exponent) (scale_nonzero : scale ≠ 0)
    (coefficient firstLeft firstScale secondRight secondScale : ℝ) (point : ℝ × ℝ) :
    HasStrictFDerivAt
      (normalizedCylinderSource exponent coefficient scale firstLeft firstScale secondRight secondScale)
      ((exponent*firstScale*(firstLeft+firstScale*point.1)^(exponent-1)) •
        ContinuousLinearMap.fst ℝ ℝ ℝ +
       (coefficient*secondScale*(1-scale*secondRight+scale*secondScale*point.2)^(exponent-1)) •
        ContinuousLinearMap.snd ℝ ℝ ℝ) point := by
  have first_affine_derivative :=
    ((hasStrictFDerivAt_fst (𝕜 := ℝ) (p := point)).const_mul firstScale).const_add firstLeft
  have first_derivative := first_affine_derivative.rpow_const (Or.inr exponent_ge_one)
  have second_affine_derivative :=
    ((hasStrictFDerivAt_snd (𝕜 := ℝ) (p := point)).const_mul
      (scale*secondScale)).const_add (1-scale*secondRight)
  have second_power_derivative := second_affine_derivative.rpow_const (Or.inr exponent_ge_one)
  have second_derivative :=
    (second_power_derivative.sub_const 1).const_mul (coefficient/(exponent*scale))
  have sum_derivative := first_derivative.add second_derivative
  simp only [smul_smul] at sum_derivative
  have first_coefficient : exponent*(firstLeft+firstScale*point.1)^(exponent-1)*firstScale =
      exponent*firstScale*(firstLeft+firstScale*point.1)^(exponent-1) := by ring
  have second_coefficient : coefficient/(exponent*scale)*
      (exponent*(1-scale*secondRight+scale*secondScale*point.2)^(exponent-1)*(scale*secondScale)) =
      coefficient*secondScale*(1-scale*secondRight+scale*secondScale*point.2)^(exponent-1) := by
    have exponent_nonzero : exponent ≠ 0 := by linarith
    field_simp [exponent_nonzero, scale_nonzero]
    <;> ring
  rw [first_coefficient, second_coefficient] at sum_derivative
  exact sum_derivative

end LambdaCantor.Last
