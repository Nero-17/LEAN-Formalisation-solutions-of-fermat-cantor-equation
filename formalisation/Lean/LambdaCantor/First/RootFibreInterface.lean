import LambdaCantor.First.RootsMeasures
import LambdaCantor.Addresses
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Planned root-fibre interface — the analytic theorem is NOT yet proved

This file defines concrete input data and a target proposition only.
It contains no axiom, sorry, or theorem asserting the root-fibre conclusion.
Planned theorem: LambdaCantor.First.Roots.root_fibres (data : RootFibreData exponent)
  : RootFibreConclusion data.
-/
noncomputable section
namespace LambdaCantor.First.Roots

open MeasureTheory

def cylinderCoordinate (word : ℕ → Bool) (length : ℕ) (tail : ℕ → Bool) (ratio : ℝ) : ℝ :=
  prefixValue ratio word length + ratio ^ length * address ratio tail

def cylinderResidual (exponent : ℝ) (leftWord rightWord : ℕ → Bool)
    (leftLength rightLength : ℕ) (digits : ℕ → Bool × Bool) (ratio : ℝ) : ℝ :=
  cylinderCoordinate leftWord leftLength (fun index => (digits index).1) ratio ^ exponent +
    cylinderCoordinate rightWord rightLength (fun index => (digits index).2) ratio ^ exponent - 1

/-- Concrete hypotheses of manuscript Lemma root-fibres. Positivity is required
on the full parameter band; uniqueness is required only within that band.
The root map itself need not be supplied with a continuity assumption. -/
structure RootFibreData (exponent : ℝ) where
  exponent_gt_one : 1 < exponent
  lower : ℝ
  upper : ℝ
  lower_gt_quarter : 1 / 4 < lower
  upper_lt_half : upper < 1 / 2
  ordered : lower ≤ upper
  leftWord : ℕ → Bool
  rightWord : ℕ → Bool
  leftLength : ℕ
  rightLength : ℕ
  root : (ℕ → Bool × Bool) → ℝ
  root_in_band : ∀ digits, root digits ∈ Set.Icc lower upper
  left_positive : ∀ (digits : ℕ → Bool × Bool) (ratio : ℝ), ratio ∈ Set.Icc lower upper →
    0 < cylinderCoordinate leftWord leftLength (fun index => (digits index).1) ratio
  right_positive : ∀ (digits : ℕ → Bool × Bool) (ratio : ℝ), ratio ∈ Set.Icc lower upper →
    0 < cylinderCoordinate rightWord rightLength (fun index => (digits index).2) ratio
  unique_root : ∀ digits ratio, ratio ∈ Set.Icc lower upper →
    (cylinderResidual exponent leftWord rightWord leftLength rightLength digits ratio = 0 ↔
      ratio = root digits)
  derivative_lower_bound : ℝ
  derivative_lower_bound_positive : 0 < derivative_lower_bound
  transverse : ∀ digits, derivative_lower_bound ≤
    |deriv (cylinderResidual exponent leftWord rightWord leftLength rightLength digits) (root digits)|

/-- Target conclusion only. This definition is not a proof of absolute
continuity or of the dimension statement. -/
def RootFibreConclusion {exponent : ℝ} (data : RootFibreData exponent) : Prop :=
  rootLaw data.root ≪ volume ∧
    ∀ᵐ ratio ∂rootLaw data.root,
      dimH (intersection exponent ratio) = ENNReal.ofReal (expectedDimension ratio)

end LambdaCantor.First.Roots

