import LambdaCantor.AE.ConvolutionMeasureCore
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace LambdaCantor.AE.ExternalPlancherel

/-!
Registered external classical results, authorized in round R025. These are
general Fourier-analysis results, with no Cantor, parameter-family, annular,
Newton-kernel, or dimension hypotheses or conclusions.

Primary sources checked 2026-10-24:

* Károly Simon, `Fractals and Fourier analysis`, File C, Theorem 4.3,
  slide 83: a finite Borel measure on R with Fourier transform in L2 has
  an L2 density. Slides 84–86 give Mattila's proof and identify the source
  as Pertti Mattila, `Fourier Analysis and Hausdorff Dimension` (2015),
  Theorem 3.3, p.31.
  https://math.bme.hu/~simonk/ff/2017_C_8_uj.pdf

* Gautam Iyer, `Lecture Notes on Measure Theory`, Fall 2022, section 11.3,
  Theorem 11.16, p.22: the Fourier transform is a bijective linear L2
  isometry, with the exp(-2*pi*i*x*frequency) convention of section 11.1.
  https://www.math.cmu.edu/~gautam/sj/teaching/2022-23/720-measure/pdfs/measure-tablet.pdf

The norm identity below is Plancherel with this exact convention. For a
positive finite measure its density is nonnegative almost everywhere and
belongs to L1, with integral equal to the finite measure's total mass.
The second statement is the standard converse Plancherel corollary: the
inverse L2 transform of the actual L1 transform equals the original L1
function by Fourier inversion/uniqueness. It does not assume an unrelated
abstract transform agrees with the integral transform.
-/

axiom finite_measure_L2_density (measure : Measure ℝ) [IsFiniteMeasure measure]
    (fourier_square_integrable : MemLp (measureFourier measure) 2 volume) :
    ∃ density : ℝ → ℝ, Integrable density volume ∧ MemLp density 2 volume ∧
      (∀ᵐ point : ℝ, 0 ≤ density point) ∧
      measure = volume.withDensity (fun point => ENNReal.ofReal (density point)) ∧
      (∫ point : ℝ, |density point|^2) =
        ∫ frequency : ℝ, ‖measureFourier measure frequency‖^2

axiom complex_L1_of_fourier_L2 (function : ℝ → ℂ)
    (integrable : Integrable function volume)
    (fourier_square_integrable : MemLp (𝓕 function) 2 volume) :
    MemLp function 2 volume ∧
      (∫ point : ℝ, ‖function point‖^2) = ∫ frequency : ℝ, ‖𝓕 function frequency‖^2

end LambdaCantor.AE.ExternalPlancherel
