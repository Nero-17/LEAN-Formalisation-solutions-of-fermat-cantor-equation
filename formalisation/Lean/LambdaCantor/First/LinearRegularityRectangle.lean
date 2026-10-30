import LambdaCantor.First.LinearRegularityDenseL2
import LambdaCantor.First.LinearRegularitySparseFourier
import LambdaCantor.First.LinearRegularityProduct
import LambdaCantor.First.RootsLinearSobolev

noncomputable section
open MeasureTheory
namespace LambdaCantor.First.LinearRegularity

/-- An actual L2 density and positive weighted characteristic-function
energy, an explicit positive Sobolev regularity criterion. -/
def HasPositiveSobolevDensity (measure : Measure ℝ) : Prop :=
  HasL2Density measure ∧ ∃ order : ℝ, 0 < order ∧
    Integrable (fun frequency : ℝ => (1 + frequency ^ 2) ^ order * ‖charFun measure frequency‖ ^ 2)

theorem HasL2Density.conv_power_decay {dense sparse : Measure ℝ}
    [IsProbabilityMeasure dense] [IsProbabilityMeasure sparse]
    (hdense : HasL2Density dense) (hsparse : HasPowerFourierDecay sparse) :
    HasPositiveSobolevDensity (dense ∗ sparse) := by
  obtain ⟨density, hnonnegative, hmeasurable, hintegrable, hsquare, hlaw⟩ := hdense
  obtain ⟨order, constant, horder, hconstant, hdecay⟩ := hsparse
  haveI : IsProbabilityMeasure (volume.withDensity (fun point => ENNReal.ofReal (density point))) :=
    hlaw ▸ inferInstance
  rw [hlaw]
  refine ⟨Roots.convolution_has_l2_density sparse density hnonnegative hmeasurable hintegrable hsquare,
    order, horder, ?_⟩
  exact Roots.real_density_convolution_weighted_energy sparse density hnonnegative hmeasurable
    hintegrable hsquare order constant horder hconstant.le
    (fun frequency hfrequency => hdecay frequency hfrequency.le)

/-- The actual paired projected Cantor law has positive Sobolev regularity
off a dimension-at-most-one set on each supercritical parameter rectangle. -/
theorem projected_law_regular_rectangle {lower upper lowerSlope upperSlope : ℝ}
    (hlower : (1 / 4 : ℝ) < lower) (hordered : lower < upper) (hupper : upper < 1 / 2)
    (hslopes : lowerSlope < upperSlope) :
    ∃ exceptional : Set (ℝ × ℝ), dimH exceptional ≤ 1 ∧
      ∀ parameter ∈ Set.Ioo lower upper ×ˢ Set.Ioo lowerSlope upperSlope,
        parameter ∉ exceptional →
        HasPositiveSobolevDensity (Roots.pairedAddressMeasure.map (pairedProjection parameter.1 parameter.2)) := by
  obtain ⟨blockLength, hblock, hsurplus⟩ := exists_supercritical_block_length hlower
  have hblockTwo : 2 ≤ blockLength := by
    by_contra hnot
    have hone : blockLength = 1 := by omega
    subst blockLength
    norm_num at hsurplus
    linarith
  have hlowerPos : 0 < lower := lt_trans (by norm_num) hlower
  obtain ⟨denseException, hdenseDimension, hdense⟩ :=
    denseProjection_generic_l2 hlowerPos hordered hupper hslopes blockLength hblockTwo hsurplus
  obtain ⟨sparseException, hsparseDimension, hsparse⟩ := sparseProjection_generic_fourier
  let sparseParameters : Set (ℝ × ℝ) :=
    {ratio : ℝ | 0 < ratio ∧ ratio ^ blockLength ∈ sparseException} ×ˢ Set.univ
  have hsparseParameters : dimH sparseParameters ≤ 1 :=
    dimH_zero_exception_times_real _
      (dimH_positive_power_preimage sparseException hsparseDimension blockLength (by omega))
  refine ⟨denseException ∪ sparseParameters, ?_, ?_⟩
  · rw [dimH_union]
    exact max_le hdenseDimension hsparseParameters
  intro parameter hparameter houtside
  have hpositive := hlowerPos.trans hparameter.1.1
  have hlt : parameter.1 < 1 := hparameter.1.2.trans (hupper.trans (by norm_num))
  have hdensity := hdense parameter hparameter (fun h => houtside (Or.inl h))
  have hdecay := hsparse parameter.1 parameter.2 blockLength hpositive hlt (by omega) (by
    intro h
    exact houtside (Or.inr ⟨⟨hpositive, h⟩, Set.mem_univ _⟩))
  letI : IsProbabilityMeasure (Roots.pairedAddressMeasure.map
      (denseProjection parameter.1 parameter.2 blockLength)) :=
    Measure.isProbabilityMeasure_map (measurable_denseProjection hpositive.le hlt _ _).aemeasurable
  letI : IsProbabilityMeasure (Roots.pairedAddressMeasure.map
      (sparseProjection parameter.1 parameter.2 blockLength)) :=
    Measure.isProbabilityMeasure_map (measurable_sparseProjection hpositive.le hlt _ _).aemeasurable
  rw [pairedProjection_law_convolution hpositive.le hlt parameter.2 blockLength, Measure.conv_comm]
  exact hdensity.conv_power_decay hdecay

end LambdaCantor.First.LinearRegularity
