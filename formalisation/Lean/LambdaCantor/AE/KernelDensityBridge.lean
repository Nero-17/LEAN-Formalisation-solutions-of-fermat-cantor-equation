import LambdaCantor.AE.KernelMass
import LambdaCantor.AE.DensityContradiction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Filter MeasureTheory Metric Set
open scoped Topology ENNReal

namespace LambdaCantor.AE

/-- The real mass bound gives a scale-independent positive fraction of a
parameter ball. The factor eight includes the real ball's length 2*radius. -/
theorem proportion_lower_of_real_measure_lower
    (good : Set ℝ) (centre : ℝ) {radius constant : ℝ}
    (hradius : 0 < radius) (hconstant : 0 < constant)
    (hmeasure : radius / (4 * constant) ≤
      volume.real (good ∩ closedBall centre radius)) :
    ENNReal.ofReal (1 / (8 * constant)) ≤
      volume (good ∩ closedBall centre radius) / volume (closedBall centre radius) := by
  apply ENNReal.ofReal_le_of_le_toReal
  rw [ENNReal.toReal_div, Real.volume_closedBall,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * radius)]
  change 1 / (8 * constant) ≤
    volume.real (good ∩ closedBall centre radius) / (2 * radius)
  apply (le_div_iff₀ (by positivity : 0 < 2 * radius)).mpr
  calc
    (1 / (8 * constant)) * (2 * radius) = radius / (4 * constant) := by
      field_simp [ne_of_gt hconstant]
      <;> ring
    _ ≤ _ := hmeasure

/-- Terminal kernel-to-density implication of the almost-everywhere argument.
The analytic kernel estimates are hypotheses, and the measure conclusion is
proved from Cauchy--Schwarz and Lebesgue differentiation. -/
theorem ae_mem_of_local_kernel_estimates
    (good domain : Set ℝ) (hmeasurable : MeasurableSet good)
    (hlocal : ∀ᵐ centre ∂volume, centre ∈ domain →
      ∃ (radii : ℕ → ℝ) (constant : ℝ) (density : ℕ → Lp ℝ 2 volume),
        0 < constant ∧ (∀ depth, 0 < radii depth) ∧
        Tendsto radii atTop (𝓝[>] 0) ∧
        ∀ᶠ depth in atTop,
          (1 / 2 ≤ ∫ point in good ∩ closedBall centre (radii depth), density depth point) ∧
          ‖density depth‖ ^ 2 ≤ constant / radii depth) :
    ∀ᵐ centre ∂volume, centre ∈ domain → centre ∈ good := by
  apply ae_mem_of_local_positive_proportion good domain hmeasurable
  filter_upwards [hlocal] with centre hcentre
  intro hdomain
  obtain ⟨radii, constant, density, hconstant, hradii, hlimit, hestimates⟩ :=
    hcentre hdomain
  refine ⟨radii, ENNReal.ofReal (1 / (8 * constant)), ?_, hlimit, ?_⟩
  · exact ENNReal.ofReal_pos.mpr (by positivity)
  filter_upwards [hestimates] with depth hdepth
  apply proportion_lower_of_real_measure_lower good centre (hradii depth) hconstant
  apply measure_lower_of_kernel_mass volume (density depth)
    (hmeasurable.inter isClosed_closedBall.measurableSet)
    (ne_top_of_le_ne_top ?_ (measure_mono inter_subset_right))
    (hradii depth) hconstant hdepth.1 hdepth.2
  rw [Real.volume_closedBall]
  exact ENNReal.ofReal_ne_top

end LambdaCantor.AE
