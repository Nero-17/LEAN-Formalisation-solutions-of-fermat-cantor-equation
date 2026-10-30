import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

namespace LambdaCantor

/-- The address map in Definition 1.1, indexed from zero. -/
def address (ratio : ℝ) (digits : ℕ → Bool) : ℝ :=
  (1 - ratio) * ∑' j : ℕ, (if digits j then (1 : ℝ) else 0) * ratio ^ j

/-- The contraction-ratio Cantor set in the frozen source. -/
def cantorSet (ratio : ℝ) : Set ℝ := Set.range (address ratio)

/-- Real exponents are interpreted using real powers. -/
def intersection (exponent ratio : ℝ) : Set (ℝ × ℝ) :=
  {point | point.1 ∈ cantorSet ratio ∧ point.2 ∈ cantorSet ratio ∧
    point.1 ^ exponent + point.2 ^ exponent = 1}

def firstTransition (exponent : ℝ) : ℝ :=
  sInf {ratio | ratio ∈ Set.Ioc (0 : ℝ) (1 / 2) ∧
    0 < dimH (intersection exponent ratio)}

def lastTransition (exponent : ℝ) : ℝ :=
  sSup {ratio | ratio ∈ Set.Ioc (0 : ℝ) (1 / 2) ∧
    dimH (intersection exponent ratio) = 0}

def expectedDimension (ratio : ℝ) : ℝ :=
  2 * Real.log 2 / Real.log (1 / ratio) - 1

theorem zero_mem_cantorSet (ratio : ℝ) : 0 ∈ cantorSet ratio := by
  refine ⟨fun _ => false, ?_⟩
  simp [address]

end LambdaCantor
