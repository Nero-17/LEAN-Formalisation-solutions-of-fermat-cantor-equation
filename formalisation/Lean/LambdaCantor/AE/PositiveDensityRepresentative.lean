import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace LambdaCantor.AE

def positiveDensityRepresentative (density : ℝ → ℝ) : ℝ → ℝ := fun value => max 0 (density value)

theorem positiveDensityRepresentative_nonnegative (density : ℝ → ℝ) (value : ℝ) :
    0 ≤ positiveDensityRepresentative density value := le_max_left _ _

theorem positiveDensityRepresentative_ae_eq {density : ℝ → ℝ}
    (nonnegative : ∀ᵐ value : ℝ, 0 ≤ density value) :
    positiveDensityRepresentative density =ᵐ[volume] density := by
  filter_upwards [nonnegative] with value value_nonnegative
  exact max_eq_right value_nonnegative

theorem positiveDensityRepresentative_integrable {density : ℝ → ℝ}
    (integrable : Integrable density) (nonnegative : ∀ᵐ value : ℝ, 0 ≤ density value) :
    Integrable (positiveDensityRepresentative density) :=
  integrable.congr (positiveDensityRepresentative_ae_eq nonnegative).symm

theorem positiveDensityRepresentative_memLp {density : ℝ → ℝ} {power : ℝ≥0∞}
    (square_integrable : MemLp density power volume) (nonnegative : ∀ᵐ value : ℝ, 0 ≤ density value) :
    MemLp (positiveDensityRepresentative density) power volume :=
  square_integrable.ae_eq (positiveDensityRepresentative_ae_eq nonnegative).symm

theorem positiveDensityRepresentative_support (density : ℝ → ℝ) :
    Function.support (positiveDensityRepresentative density) ⊆ Function.support density := by
  intro value membership
  show density value ≠ 0
  intro zero
  exact membership (by simp only [positiveDensityRepresentative, zero, max_self])

end LambdaCantor.AE
