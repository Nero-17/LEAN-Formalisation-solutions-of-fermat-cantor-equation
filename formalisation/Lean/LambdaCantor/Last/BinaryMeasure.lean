import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic.NormNum

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.Last

/-- The fair bit measure used for each strict-return branching choice. -/
def fairBit : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac false + (2 : ℝ≥0∞)⁻¹ • Measure.dirac true

instance fairBit_probability : IsProbabilityMeasure fairBit := by
  constructor
  norm_num [fairBit, Measure.add_apply, Measure.smul_apply]
  rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

@[simp] theorem fairBit_singleton (bit : Bool) : fairBit {bit} = (2 : ℝ≥0∞)⁻¹ := by
  cases bit <;> norm_num [fairBit, Measure.add_apply, Measure.smul_apply]

/-- Independent fair branching choices. -/
def binaryBranchMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => fairBit)

instance binaryBranchMeasure_probability : IsProbabilityMeasure binaryBranchMeasure := by
  unfold binaryBranchMeasure
  infer_instance

/-- A finite prefix cylinder in the binary tree. -/
def branchCylinder (depth : ℕ) (branch : ℕ → Bool) : Set (ℕ → Bool) :=
  {other | ∀ position < depth, other position = branch position}

@[simp] theorem binaryBranchMeasure_cylinder (depth : ℕ) (branch : ℕ → Bool) :
    binaryBranchMeasure (branchCylinder depth branch) = (2 : ℝ≥0∞)⁻¹ ^ depth := by
  have hset : branchCylinder depth branch =
      (↑(Finset.range depth) : Set ℕ).pi (fun position => {branch position}) := by
    ext other
    simp [branchCylinder, Set.mem_pi]
  rw [hset, binaryBranchMeasure, Measure.infinitePi_pi]
  · simp
  · intro position _
    exact measurableSet_singleton _

end LambdaCantor.Last

