import Mathlib.Analysis.Fourier.FourierTransform

noncomputable section
open MeasureTheory

namespace LambdaCantor.First.Roots.External

/-!
External classical theorem, not an axiom for any result of the manuscript.

Source checked 2026-10-21: Terence Tao, "247B, Notes 1: Restriction theory",
29 March 2020, introductory equations (1) and (3):
https://terrytao.wordpress.com/2020/03/29/247b-notes-1-restriction-theory/

Equation (1) defines the transform of an L1 function by the integral with
exp(-2*pi*i*x*frequency). Equation (3) asserts equality of L2 norms for
functions in L1 intersect L2. The statement below is its dimension-one,
complex-valued specialization, with the norm equality squared. The MemLp
conclusion records that the actual integral transform lies in L2. Mathlib's
Real.fourierChar/inner product integral uses exactly this normalization.

Mathlib also proves abstract L2 Plancherel in Analysis/Fourier/LpSpace.lean;
using this external input avoids treating the missing identification of the
abstract L2 transform with the actual L1 integral as an internal proved fact.
-/

axiom classical_plancherel_l1_l2 (function : ℝ → ℂ)
    (integrable : Integrable function volume) (square_integrable : MemLp function 2 volume) :
    MemLp (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) function) 2 volume ∧
      (∫ frequency : ℝ,
        ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
          function frequency‖ ^ 2) =
        ∫ point : ℝ, ‖function point‖ ^ 2

end LambdaCantor.First.Roots.External
