import LambdaCantor.AE.AveragedFullEnergy
import LambdaCantor.AE.ParameterCutoffCover

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

namespace LambdaCantor.AE

/-- The averaging estimate supplies local integrability, not merely almost
everywhere finiteness. This is the input needed for Lebesgue-point freezing. -/
theorem locallyIntegrableOn_fullFourierEnergy
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1) :
    LocallyIntegrableOn (fun ratio => (fullFourierEnergy ratio regularity).toReal)
      (Ioo lower upper) volume := by
  intro ratio hratio
  have hfinite := lintegral_cutoff_fullFourierEnergy_lt_top hlower horder hupper hregularity hrange
    (interiorParameterBump ⟨ratio, hratio⟩)
    (interiorParameterBump ⟨ratio, hratio⟩).contDiff
    (interiorParameterBump ⟨ratio, hratio⟩).hasCompactSupport
    (interiorParameterBump_support ⟨ratio, hratio⟩)
    (fun parameter => (interiorParameterBump ⟨ratio, hratio⟩).nonneg)
  have hintegrable := integrable_toReal_of_lintegral_ne_top
    (((interiorParameterBump ⟨ratio, hratio⟩).continuous.measurable.ennreal_ofReal.mul
      (measurable_fullFourierEnergy regularity)).aemeasurable) hfinite.ne
  refine ⟨ball ratio (interiorParameterBump ⟨ratio, hratio⟩).rIn,
    mem_nhdsWithin_of_mem_nhds
      (ball_mem_nhds ratio (interiorParameterBump ⟨ratio, hratio⟩).rIn_pos), ?_⟩
  apply hintegrable.integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_ball] with parameter hparameter
  change (ENNReal.ofReal (interiorParameterBump ⟨ratio, hratio⟩ parameter) *
    fullFourierEnergy parameter regularity).toReal = (fullFourierEnergy parameter regularity).toReal
  rw [(interiorParameterBump ⟨ratio, hratio⟩).one_of_mem_closedBall
    (ball_subset_closedBall hparameter)]
  simp only [ENNReal.ofReal_one, one_mul]

end LambdaCantor.AE
