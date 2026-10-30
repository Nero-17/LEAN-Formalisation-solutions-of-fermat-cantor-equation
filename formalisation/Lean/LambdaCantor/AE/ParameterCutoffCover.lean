import LambdaCantor.AE.ConvolutionFourierL2
import LambdaCantor.AE.MathlibBumpInnerProduct
import Mathlib.Topology.Compactness.Lindelof

noncomputable section
open Set MeasureTheory Filter Metric

namespace LambdaCantor.AE

def interiorParameterBump {lower upper : ℝ} (point : Ioo lower upper) : ContDiffBump (point : ℝ) where
  rIn := min ((point : ℝ) - lower) (upper - (point : ℝ)) / 4
  rOut := min ((point : ℝ) - lower) (upper - (point : ℝ)) / 2
  rIn_pos := div_pos
    (lt_min (sub_pos.mpr point.property.1) (sub_pos.mpr point.property.2)) (by norm_num)
  rIn_lt_rOut := by
    have hpositive : 0 < min ((point : ℝ) - lower) (upper - (point : ℝ)) :=
      lt_min (sub_pos.mpr point.property.1) (sub_pos.mpr point.property.2)
    linarith

theorem interiorParameterBump_support {lower upper : ℝ} (point : Ioo lower upper) :
    tsupport (interiorParameterBump point : ℝ → ℝ) ⊆ Ioo lower upper := by
  rw [(interiorParameterBump point).tsupport_eq]
  intro ratio hratio
  have hdist : |ratio - (point : ℝ)| ≤
      min ((point : ℝ) - lower) (upper - (point : ℝ)) / 2 := by
    simpa only [mem_closedBall, Real.dist_eq, interiorParameterBump] using hratio
  have habs := abs_le.mp hdist
  have hleft := min_le_left ((point : ℝ) - lower) (upper - (point : ℝ))
  have hright := min_le_right ((point : ℝ) - lower) (upper - (point : ℝ))
  have hpoint := point.property
  constructor <;> linarith only [hpoint.1, hpoint.2, habs.1, habs.2, hleft, hright]

theorem interiorParameterBump_positive {lower upper : ℝ} (point : Ioo lower upper) :
    0 < interiorParameterBump point (point : ℝ) := by
  have hone : interiorParameterBump point (point : ℝ) = 1 :=
    (interiorParameterBump point).one_of_mem_closedBall (by simp [(interiorParameterBump point).rIn_pos.le])
  rw [hone]
  norm_num

/-- A countable subcover removes the parameter cutoff from the actual full-energy conclusion. -/
theorem ae_finite_fullFourierEnergy_on_interval
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1) :
    ∀ᵐ ratio : ℝ, ratio ∈ Ioo lower upper → fullFourierEnergy ratio regularity < ⊤ := by
  have hlocal (point : Ioo lower upper) :
      ∀ᵐ ratio : ℝ, 0 < interiorParameterBump point ratio → fullFourierEnergy ratio regularity < ⊤ :=
    ae_finite_fullFourierEnergy hlower horder hupper hregularity hrange
      (interiorParameterBump point) (interiorParameterBump point).contDiff
      (interiorParameterBump point).hasCompactSupport (interiorParameterBump_support point)
      (fun ratio => (interiorParameterBump point).nonneg)
  obtain ⟨cover, hcountable, hcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof (Ioo lower upper)).elim_countable_subcover
      (fun point : Ioo lower upper => {ratio : ℝ | 0 < interiorParameterBump point ratio})
      (fun point => isOpen_lt continuous_const (interiorParameterBump point).continuous)
      (by intro ratio hratio; exact mem_iUnion.mpr ⟨⟨ratio, hratio⟩, interiorParameterBump_positive _⟩)
  letI : Countable cover := hcountable.to_subtype
  have hall : ∀ᵐ ratio : ℝ, ∀ point : cover,
      0 < interiorParameterBump point.val ratio → fullFourierEnergy ratio regularity < ⊤ :=
    ae_all_iff.mpr (fun point => hlocal point.val)
  filter_upwards [hall] with ratio hratio
  intro hinside
  obtain ⟨point, hpoint, hpositive⟩ := mem_iUnion₂.mp (hcover hinside)
  exact hratio ⟨point, hpoint⟩ hpositive

theorem ae_convolutionFourier_memLp_two_on_interval
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1) :
    ∀ᵐ ratio : ℝ, ratio ∈ Ioo lower upper →
      MemLp (measureFourier (selfConvolutionProbability ratio)) 2 volume := by
  filter_upwards [ae_finite_fullFourierEnergy_on_interval hlower horder hupper hregularity hrange]
    with ratio hfinite
  exact fun hinside => convolutionFourier_memLp_two_of_fullEnergy (hfinite hinside)

end LambdaCantor.AE
