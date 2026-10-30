import LambdaCantor.AE.ConvolutionMeasureCore
import LambdaCantor.AE.FullFourierEnergy

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace LambdaCantor.AE
theorem fullFourierEnergy_eq_convolution_energy (ratio regularity : ℝ) :
    fullFourierEnergy ratio regularity =
      ∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) *
        ‖measureFourier (selfConvolutionProbability ratio) frequency‖ ^ 2) := by
  simp only [fullFourierEnergy, norm_measureFourier_selfConvolution_sq]

end LambdaCantor.AE

