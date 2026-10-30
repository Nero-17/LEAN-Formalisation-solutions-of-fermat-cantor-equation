import LambdaCantor.Last.NormalizedCylinder
import LambdaCantor.Classical.DerivativeLocalization
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor.RealPowers
open Last

theorem normalized_source_horizontal_derivative {exponent : ℝ}
    (exponent_ge_one : 1 ≤ exponent)
    (coefficient scale firstLeft firstScale secondRight secondScale height x y : ℝ) :
    HasDerivAt (fun coordinate => normalizedCylinderSource exponent coefficient scale
      firstLeft firstScale secondRight secondScale (coordinate,y)/height)
      ((exponent*firstScale*(firstLeft+firstScale*x)^(exponent-1))/height) x := by
  have derivative := (((((hasDerivAt_id x).const_mul firstScale).const_add firstLeft).rpow_const
    (p := exponent) (Or.inr exponent_ge_one)).add_const
      (coefficient/(exponent*scale)*((1-scale*secondRight+scale*secondScale*y)^exponent-1))).div_const height
  convert! derivative using 1 <;> simp only [normalizedCylinderSource, id_eq, mul_one] <;> ring

theorem normalized_source_vertical_derivative {exponent scale : ℝ}
    (exponent_ge_one : 1 ≤ exponent) (scale_nonzero : scale ≠ 0)
    (coefficient firstLeft firstScale secondRight secondScale height x y : ℝ) :
    HasDerivAt (fun coordinate => normalizedCylinderSource exponent coefficient scale
      firstLeft firstScale secondRight secondScale (x,coordinate)/height)
      ((coefficient*secondScale*
        (1-scale*secondRight+scale*secondScale*y)^(exponent-1))/height) y := by
  have derivative := (((((((hasDerivAt_id y).const_mul (scale*secondScale)).const_add
    (1-scale*secondRight)).rpow_const (p := exponent) (Or.inr exponent_ge_one)).sub_const 1).const_mul
      (coefficient/(exponent*scale))).const_add
        ((firstLeft+firstScale*x)^exponent)).div_const height
  have exponent_nonzero : exponent ≠ 0 := by linarith
  convert! derivative using 1 <;> simp only [normalizedCylinderSource, id_eq, mul_one]
  all_goals first
    | (funext coordinate; ring)
    | (apply congrArg (fun value : ℝ => value/height)
       field_simp [exponent_nonzero, scale_nonzero]
       <;> ring)

end LambdaCantor.RealPowers

