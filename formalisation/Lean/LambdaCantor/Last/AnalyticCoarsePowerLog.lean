import LambdaCantor.Last.RealPowerLimit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

/-- The actual normalized power drop, with derivative tending to one. -/
def coarseNormalizedPowerDrop (exponent scale coordinate : ℝ) : ℝ :=
  (1 - (1 - scale * coordinate) ^ exponent) / (exponent * scale)

/-- The actual logarithmic perturbation used in the coarse endpoint source. -/
def coarsePowerLog (exponent scale coordinate : ℝ) : ℝ :=
  Real.log (coarseNormalizedPowerDrop exponent scale coordinate)

def coarsePowerFactor (exponent scale coordinate : ℝ) : ℝ :=
  (1 - scale * coordinate) ^ (exponent - 1)

def coarseLogCoordinateMap (exponent scale coordinate : ℝ) : ℝ :=
  coarsePowerLog exponent scale (Real.exp coordinate)

theorem coarseNormalizedPowerDrop_continuous {exponent : ℝ} (hexponent : 1 ≤ exponent)
    (scale : ℝ) : Continuous (coarseNormalizedPowerDrop exponent scale) := by
  unfold coarseNormalizedPowerDrop
  apply Continuous.div_const
  exact continuous_const.sub
    ((continuous_const.sub (continuous_const.mul continuous_id)).rpow_const (fun _ => Or.inr (by linarith)))

theorem coarseNormalizedPowerDrop_hasDerivAt {exponent scale : ℝ}
    (hexponent : 1 < exponent) (hscale : scale ≠ 0) (coordinate : ℝ) :
    HasDerivAt (coarseNormalizedPowerDrop exponent scale)
      (coarsePowerFactor exponent scale coordinate) coordinate := by
  have haffine := ((hasDerivAt_id coordinate).const_mul scale).const_sub (1 : ℝ)
  have hpower := haffine.rpow_const (p := exponent) (Or.inr hexponent.le)
  have hdrop := (hpower.const_sub (1 : ℝ)).div_const (exponent * scale)
  convert! hdrop using 1 <;>
    first
    | rfl
    | (simp [coarseNormalizedPowerDrop, coarsePowerFactor] <;>
        field_simp [hscale, ne_of_gt (show 0 < exponent by linarith)] <;> ring)

theorem coarsePowerLog_hasDerivAt {exponent scale coordinate : ℝ}
    (hexponent : 1 < exponent) (hscale : scale ≠ 0)
    (hpositive : 0 < coarseNormalizedPowerDrop exponent scale coordinate) :
    HasDerivAt (coarsePowerLog exponent scale)
      (coarsePowerFactor exponent scale coordinate / coarseNormalizedPowerDrop exponent scale coordinate) coordinate := by
  have hlog := (coarseNormalizedPowerDrop_hasDerivAt hexponent hscale coordinate).log hpositive.ne'
  convert! hlog using 1 <;>
    first | rfl | simp [coarsePowerLog, div_eq_mul_inv, mul_comm]

theorem coarseLogCoordinateMap_hasDerivAt {exponent scale coordinate : ℝ}
    (hexponent : 1 < exponent) (hscale : scale ≠ 0)
    (hpositive : 0 < coarseNormalizedPowerDrop exponent scale (Real.exp coordinate)) :
    HasDerivAt (coarseLogCoordinateMap exponent scale)
      (Real.exp coordinate * coarsePowerFactor exponent scale (Real.exp coordinate) /
        coarseNormalizedPowerDrop exponent scale (Real.exp coordinate)) coordinate := by
  have hcomposition := (coarsePowerLog_hasDerivAt hexponent hscale hpositive).comp coordinate
    (Real.hasDerivAt_exp coordinate)
  convert! hcomposition using 1 <;>
    first | rfl | ring

theorem coarseNormalizedPowerDrop_limit {exponent : ℝ} (hexponent : exponent ≠ 0) (coordinate : ℝ) :
    Tendsto (fun scale : ℝ => coarseNormalizedPowerDrop exponent scale coordinate)
      (𝓝[>] 0) (𝓝 coordinate) := by
  have hlimit := (real_power_drop_limit exponent coordinate).div_const exponent
  have hvalue : exponent * coordinate / exponent = coordinate := by field_simp [hexponent]
  have hidentity : (fun scale : ℝ => coarseNormalizedPowerDrop exponent scale coordinate) =
      fun scale => ((1 - (1 - scale * coordinate) ^ exponent) / scale) / exponent := by
    funext scale
    simp only [coarseNormalizedPowerDrop, div_div, mul_comm]
  rw [hidentity]
  simpa only [hvalue] using hlimit

theorem coarsePowerLog_limit {exponent coordinate : ℝ}
    (hexponent : exponent ≠ 0) (hcoordinate : 0 < coordinate) :
    Tendsto (fun scale : ℝ => coarsePowerLog exponent scale coordinate)
      (𝓝[>] 0) (𝓝 (Real.log coordinate)) :=
  (Real.continuousAt_log hcoordinate.ne').tendsto.comp (coarseNormalizedPowerDrop_limit hexponent coordinate)

theorem coarseLogCoordinateMap_limit {exponent : ℝ} (hexponent : exponent ≠ 0) (coordinate : ℝ) :
    Tendsto (fun scale : ℝ => coarseLogCoordinateMap exponent scale coordinate)
      (𝓝[>] 0) (𝓝 coordinate) := by
  simpa only [coarseLogCoordinateMap, Real.log_exp] using coarsePowerLog_limit hexponent (Real.exp_pos coordinate)

end LambdaCantor.Last
