import LambdaCantor.Last.NormalizedCylinder
import LambdaCantor.Last.RealPowerLimit

-- The limit proof is copied from Last.NormalizedCylinderLimits; its unrelated
-- derivative-margin import is deliberately omitted.
noncomputable section
namespace LambdaCantor.RealPowers
open Last
open Filter
open scoped Topology

theorem normalizedCylinderSource_limit {exponent coefficient : ℝ}
    (exponent_nonzero : exponent ≠ 0) {scales coefficients : ℕ → ℝ}
    (scales_positive : ∀ index, 0 < scales index)
    (scales_tendsto : Tendsto scales atTop (𝓝 0))
    (coefficients_tendsto : Tendsto coefficients atTop (𝓝 coefficient))
    (firstLeft firstScale secondRight secondScale : ℝ) (point : ℝ × ℝ) :
    Tendsto (fun index => normalizedCylinderSource exponent (coefficients index) (scales index)
      firstLeft firstScale secondRight secondScale point) atTop
      (𝓝 ((firstLeft+firstScale*point.1)^exponent-coefficient*(secondRight-secondScale*point.2))) := by
  have normalized_limit := normalized_power_curve_limit exponent_nonzero scales_positive
    scales_tendsto coefficients_tendsto (firstLeft+firstScale*point.1) (secondRight-secondScale*point.2)
  convert! normalized_limit using 1
  funext index
  unfold normalizedCylinderSource
  rw [show 1-scales index*secondRight+scales index*secondScale*point.2 =
    1-scales index*(secondRight-secondScale*point.2) by ring]
  field_simp [exponent_nonzero, (scales_positive index).ne']
  <;> ring

theorem normalizedCylinderSource_partial_limit {exponent coefficient : ℝ}
    {scales coefficients : ℕ → ℝ}
    (scales_tendsto : Tendsto scales atTop (𝓝 0))
    (coefficients_tendsto : Tendsto coefficients atTop (𝓝 coefficient))
    (secondRight secondScale : ℝ) (point : ℝ × ℝ) :
    Tendsto (fun index => coefficients index*secondScale*
      (1-scales index*secondRight+scales index*secondScale*point.2)^(exponent-1))
      atTop (𝓝 (coefficient*secondScale)) := by
  have partial_limit := (normalized_power_partial_limit (exponent := exponent)
    scales_tendsto coefficients_tendsto (secondRight-secondScale*point.2)).mul_const secondScale
  convert! partial_limit using 1
  funext index
  rw [show 1-scales index*secondRight+scales index*secondScale*point.2 =
    1-scales index*(secondRight-secondScale*point.2) by ring]
  ring

end LambdaCantor.RealPowers

