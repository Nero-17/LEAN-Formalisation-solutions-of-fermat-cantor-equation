import LambdaCantor.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section
open MeasureTheory

namespace LambdaCantor.AE

def fairDigitMeasure : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure fairDigitMeasure := by
  unfold fairDigitMeasure
  infer_instance

def addressProbability : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => fairDigitMeasure)

instance : IsProbabilityMeasure addressProbability := by
  unfold addressProbability
  infer_instance

theorem measurable_address_digits (ratio : ℝ) : Measurable (address ratio) := by
  unfold address
  apply measurable_const.mul
  apply Measurable.tsum
  intro index
  exact ((measurable_of_countable (fun digit : Bool => if digit then (1 : ℝ) else 0)).comp
    (measurable_pi_apply index)).mul measurable_const

def addressFourier (ratio frequency : ℝ) : ℂ :=
  ∫ digits, (Real.fourierChar (-(frequency * address ratio digits)) : ℂ) ∂addressProbability

end LambdaCantor.AE
