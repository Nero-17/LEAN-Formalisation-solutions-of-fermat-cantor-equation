import LambdaCantor.First.RootsKernelCoupling
import LambdaCantor.First.RootsKernels

noncomputable section
namespace LambdaCantor.First.Roots

def pairedCylinderDigits (word : ℕ → Bool × Bool) (depth : ℕ) (tail : ℕ → Bool × Bool) : ℕ → Bool × Bool :=
  fun index => if index < depth then word index else tail (index - depth)

@[simp] theorem pairedCylinderDigits_after (word tail : ℕ → Bool × Bool) (depth index : ℕ) :
    pairedCylinderDigits word depth tail (index + depth) = tail index := by
  simp [pairedCylinderDigits, show ¬index + depth < depth by omega]

theorem pairedCylinderDigits_agrees (word tail : ℕ → Bool × Bool) (depth : ℕ) :
    ∀ index < depth, word index = pairedCylinderDigits word depth tail index := by
  intro index index_lt
  simp [pairedCylinderDigits, index_lt]

theorem continuous_pairedCylinderDigits (word : ℕ → Bool × Bool) (depth : ℕ) :
    Continuous (pairedCylinderDigits word depth) := by
  apply continuous_pi
  intro index
  by_cases before : index < depth
  · simpa only [pairedCylinderDigits, if_pos before] using
      (continuous_const : Continuous (fun _ : ℕ → Bool × Bool => word index))
  · simpa only [pairedCylinderDigits, if_neg before] using
      (continuous_apply (index - depth) : Continuous (fun tail : ℕ → Bool × Bool => tail (index - depth)))

def completeRootKernel {exponent : ℝ} (data : RootFibreData exponent)
    (representative : ℕ → Bool × Bool) (depth : ℕ) (tail : ℕ → Bool × Bool) : ℝ :=
  rootKernelValue data representative (pairedCylinderDigits representative depth tail) depth

theorem completeRootKernel_formula {exponent : ℝ} (data : RootFibreData exponent)
    (representative : ℕ → Bool × Bool) (depth : ℕ) (tail : ℕ → Bool × Bool) :
    completeRootKernel data representative depth tail =
      data.root representative -
        (exponent * cylinderCoordinate data.leftWord data.leftLength (fun index => (representative index).1)
          (data.root representative) ^ (exponent - 1) * data.root representative ^ (data.leftLength + depth) /
          deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength representative)
            (data.root representative)) *
          (address (data.root representative) (fun index => (tail index).1) -
            address (data.root representative) (fun index => (representative (index + depth)).1)) -
        (exponent * cylinderCoordinate data.rightWord data.rightLength (fun index => (representative index).2)
          (data.root representative) ^ (exponent - 1) * data.root representative ^ (data.rightLength + depth) /
          deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength representative)
            (data.root representative)) *
          (address (data.root representative) (fun index => (tail index).2) -
            address (data.root representative) (fun index => (representative (index + depth)).2)) := by
  unfold completeRootKernel rootKernelValue rootKernelLinearTerm
  simp only [pairedCylinderDigits_after]
  ring

theorem rootKernelValue_depends_only_on_tail {exponent : ℝ} (data : RootFibreData exponent)
    (representative first second : ℕ → Bool × Bool) (depth : ℕ)
    (tail_agreement : ∀ index, first (index + depth) = second (index + depth)) :
    rootKernelValue data representative first depth = rootKernelValue data representative second depth := by
  unfold rootKernelValue rootKernelLinearTerm
  simp only [tail_agreement]

theorem continuous_completeRootKernel {exponent : ℝ} (data : RootFibreData exponent)
    (representative : ℕ → Bool × Bool) (depth : ℕ) :
    Continuous (completeRootKernel data representative depth) := by
  have ratio_nonnegative : 0 ≤ data.root representative := by
    linarith [data.lower_gt_quarter, (data.root_in_band representative).1]
  have ratio_lt_one : data.root representative < 1 := by
    linarith [data.upper_lt_half, (data.root_in_band representative).2]
  have left_continuous : Continuous (fun tail : ℕ → Bool × Bool =>
      address (data.root representative) (fun index => (tail index).1)) :=
    (continuous_address ratio_nonnegative ratio_lt_one).comp
      (continuous_pi (fun index => continuous_fst.comp (continuous_apply index)))
  have right_continuous : Continuous (fun tail : ℕ → Bool × Bool =>
      address (data.root representative) (fun index => (tail index).2)) :=
    (continuous_address ratio_nonnegative ratio_lt_one).comp
      (continuous_pi (fun index => continuous_snd.comp (continuous_apply index)))
  change Continuous (fun tail : ℕ → Bool × Bool => completeRootKernel data representative depth tail)
  simp_rw [completeRootKernel_formula]
  exact (continuous_const.sub (continuous_const.mul (left_continuous.sub continuous_const))).sub
    (continuous_const.mul (right_continuous.sub continuous_const))

theorem completeRootKernel_parent_child_coupling {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∃ minimumDepth : ℕ,
      ∀ (parent child : ℕ → Bool × Bool) (depth : ℕ), minimumDepth ≤ depth →
        (∀ index < depth, parent index = child index) → ∀ tail : ℕ → Bool × Bool,
        |completeRootKernel data parent depth
            (fun index => if index = 0 then child depth else tail (index - 1)) -
          completeRootKernel data child (depth + 1) tail| / data.root parent ^ depth ≤
          constant * ((depth : ℝ) + 1) * data.upper ^ depth := by
  obtain ⟨constant, constant_nonnegative, minimumDepth, coupling⟩ := rootFibreData_parent_child_kernel_coupling data
  refine ⟨constant, constant_nonnegative, minimumDepth, ?_⟩
  intro parent child depth depth_ge agreement tail
  have actual_bound := coupling parent child (pairedCylinderDigits child (depth + 1) tail) depth depth_ge
    agreement (pairedCylinderDigits_agrees child tail (depth + 1))
  have parent_identity : completeRootKernel data parent depth
      (fun index => if index = 0 then child depth else tail (index - 1)) =
      rootKernelValue data parent (pairedCylinderDigits child (depth + 1) tail) depth := by
    apply rootKernelValue_depends_only_on_tail
    intro index
    rw [pairedCylinderDigits_after]
    by_cases zero : index = 0
    · subst index
      simp [pairedCylinderDigits]
    · simp only [if_neg zero, pairedCylinderDigits,
        if_neg (show ¬index + depth < depth + 1 by omega)]
      congr 1
      omega
  rw [← parent_identity] at actual_bound
  exact actual_bound

end LambdaCantor.First.Roots
