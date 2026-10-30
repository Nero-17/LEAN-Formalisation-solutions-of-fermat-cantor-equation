import LambdaCantor.AE.NewtonMixture

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace LambdaCantor.AE

def prependNewtonDigit (digit : Bool × Bool) (tail : ℕ → Bool × Bool) (index : ℕ) : Bool × Bool :=
  if index = 0 then digit else tail (index-1)

def FrozenNewtonKernel.child (kernel : FrozenNewtonKernel) (digit : Bool × Bool) : FrozenNewtonKernel where
  freezing := kernel.freezing
  residual := kernel.residual +
    kernel.firstCoefficient*(1-kernel.freezing)*(if digit.1 then (1 : ℝ) else 0) +
    kernel.secondCoefficient*(1-kernel.freezing)*(if digit.2 then (1 : ℝ) else 0)
  parameterDerivative := kernel.parameterDerivative
  firstCoefficient := kernel.firstCoefficient*kernel.freezing
  secondCoefficient := kernel.secondCoefficient*kernel.freezing

theorem address_prependNewtonDigit_first {ratio : ℝ} (ratio_nonnegative : 0 ≤ ratio) (ratio_less_one : ratio < 1)
    (digit : Bool × Bool) (tail : ℕ → Bool × Bool) :
    address ratio (fun index => (prependNewtonDigit digit tail index).1) =
      (1-ratio)*(if digit.1 then (1 : ℝ) else 0) +
        ratio*address ratio (fun index => (tail index).1) := by
  rw [address_first_digit ratio_nonnegative ratio_less_one]
  simp [prependNewtonDigit]

theorem address_prependNewtonDigit_second {ratio : ℝ} (ratio_nonnegative : 0 ≤ ratio) (ratio_less_one : ratio < 1)
    (digit : Bool × Bool) (tail : ℕ → Bool × Bool) :
    address ratio (fun index => (prependNewtonDigit digit tail index).2) =
      (1-ratio)*(if digit.2 then (1 : ℝ) else 0) +
        ratio*address ratio (fun index => (tail index).2) := by
  rw [address_first_digit ratio_nonnegative ratio_less_one]
  simp [prependNewtonDigit]

/-- Conditioning a complete affine Newton observable on one paired digit
produces another complete affine kernel at the same freezing point. -/
theorem FrozenNewtonKernel.child_value (kernel : FrozenNewtonKernel)
    (ratio_nonnegative : 0 ≤ kernel.freezing) (ratio_less_one : kernel.freezing < 1)
    (digit : Bool × Bool) (tail : ℕ → Bool × Bool) :
    (kernel.child digit).value tail = kernel.value (prependNewtonDigit digit tail) := by
  unfold FrozenNewtonKernel.value
  rw [address_prependNewtonDigit_first ratio_nonnegative ratio_less_one,
    address_prependNewtonDigit_second ratio_nonnegative ratio_less_one]
  unfold centeredNewtonValue FrozenNewtonKernel.child
  simp only
  ring

/-- Exact splitting into four affine child kernels, indexed by the four
length-one paired words. No error or discarded constant is involved. -/
theorem FrozenNewtonKernel.law_exact_child_split (kernel : FrozenNewtonKernel)
    (ratio_nonnegative : 0 ≤ kernel.freezing) (ratio_less_one : kernel.freezing < 1) :
    kernel.law = ∑ word : Fin 1 → Bool × Bool,
      (4 : ℝ≥0∞)⁻¹ • (kernel.child (word 0)).law := by
  have reconstructed : ∀ digits : ℕ → Bool × Bool,
      (kernel.child (digits 0)).value (fun index => digits (index+1)) = kernel.value digits := by
    intro digits
    rw [kernel.child_value ratio_nonnegative ratio_less_one]
    congr 1
    funext index
    cases index with
    | zero => simp [prependNewtonDigit]
    | succ index => simp [prependNewtonDigit, Nat.succ_ne_zero]
  have combine_measurable : Measurable
      (fun pair : (Fin 1 → Bool × Bool) × (ℕ → Bool × Bool) => (kernel.child (pair.1 0)).value pair.2) :=
    measurable_from_prod_countable_right (fun word => (kernel.child (word 0)).value_measurable)
  have split := paired_prefix_observable_law 1
    (fun pair : (Fin 1 → Bool × Bool) × (ℕ → Bool × Bool) => (kernel.child (pair.1 0)).value pair.2)
    combine_measurable
  have observable_identity :
      (fun digits : ℕ → Bool × Bool =>
        (kernel.child ((fun index : Fin 1 => digits index) 0)).value (fun index => digits (index+1))) =
      kernel.value := by
    funext digits
    exact reconstructed digits
  change First.Roots.pairedAddressMeasure.map
    (fun digits : ℕ → Bool × Bool =>
      (kernel.child ((fun index : Fin 1 => digits index) 0)).value (fun index => digits (index + 1))) =
    ∑ word : Fin 1 → Bool × Bool, ((4 : ℝ≥0∞)⁻¹ ^ 1) •
      First.Roots.pairedAddressMeasure.map (fun tail : ℕ → Bool × Bool => (kernel.child (word 0)).value tail)
    at split
  rw [observable_identity] at split
  rw [kernel.law_eq_paired_map]
  simp_rw [FrozenNewtonKernel.law_eq_paired_map]
  simpa only [pow_one] using split

end LambdaCantor.AE
