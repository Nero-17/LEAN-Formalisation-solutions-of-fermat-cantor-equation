import LambdaCantor.First.RootsKernelCommonScale
import LambdaCantor.First.RootsKernelLaws

noncomputable section
namespace LambdaCantor.First.Roots

def parentFrozenCoordinate {exponent : ℝ} (data : RootFibreData exponent)
    (parent child : ℕ → Bool × Bool) (depth : ℕ) (tail : ℕ → Bool × Bool) : ℝ :=
  (completeRootKernel data parent depth (prependPairedDigit (child depth) tail) - data.root parent) /
    data.root parent ^ depth

def childFrozenCoordinate {exponent : ℝ} (data : RootFibreData exponent)
    (parent child : ℕ → Bool × Bool) (depth : ℕ) (tail : ℕ → Bool × Bool) : ℝ :=
  (completeRootKernel data child (depth + 1) tail - data.root parent) / data.root parent ^ depth

theorem continuous_parentFrozenCoordinate {exponent : ℝ} (data : RootFibreData exponent)
    (parent child : ℕ → Bool × Bool) (depth : ℕ) : Continuous (parentFrozenCoordinate data parent child depth) :=
  (((continuous_completeRootKernel data parent depth).comp
    (continuous_prependPairedDigit.comp (continuous_const.prodMk continuous_id))).sub continuous_const).div_const _

theorem continuous_childFrozenCoordinate {exponent : ℝ} (data : RootFibreData exponent)
    (parent child : ℕ → Bool × Bool) (depth : ℕ) : Continuous (childFrozenCoordinate data parent child depth) :=
  ((continuous_completeRootKernel data child (depth + 1)).sub continuous_const).div_const _

/-- The two actual kernels to be replaced are coupled on one unrestricted
fresh-tail probability space, after exactly the same parent normalization. -/
theorem parent_child_frozen_coordinate_coupling {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ constant : ℝ, 0 < constant ∧ ∃ minimumDepth : ℕ,
      ∀ (parent child : ℕ → Bool × Bool) (depth : ℕ), minimumDepth ≤ depth →
        (∀ index < depth, parent index = child index) → ∀ tail : ℕ → Bool × Bool,
        |parentFrozenCoordinate data parent child depth tail - childFrozenCoordinate data parent child depth tail| ≤
          constant * ((depth : ℝ) + 1) * data.upper ^ depth := by
  obtain ⟨constant, nonnegative, minimumDepth, coupling⟩ := completeRootKernel_parent_child_coupling data
  refine ⟨constant + 1, by linarith, minimumDepth, ?_⟩
  intro parent child depth depth_ge agreement tail
  have ratio_positive : 0 < data.root parent := by
    linarith [data.lower_gt_quarter, (data.root_in_band parent).1]
  have upper_nonnegative : 0 ≤ data.upper := by linarith [data.lower_gt_quarter, data.ordered]
  have identity : parentFrozenCoordinate data parent child depth tail - childFrozenCoordinate data parent child depth tail =
      (completeRootKernel data parent depth (prependPairedDigit (child depth) tail) -
        completeRootKernel data child (depth + 1) tail) / data.root parent ^ depth := by
    unfold parentFrozenCoordinate childFrozenCoordinate
    ring
  rw [identity, abs_div, abs_of_pos (pow_pos ratio_positive depth)]
  have estimate := coupling parent child depth depth_ge agreement tail
  change |completeRootKernel data parent depth (prependPairedDigit (child depth) tail) -
    completeRootKernel data child (depth + 1) tail| / data.root parent ^ depth ≤ _ at estimate
  apply estimate.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : constant ≤ constant + 1) (by positivity))
    (pow_nonneg upper_nonnegative depth)

/-- Both actual laws in each replacement have one uniform bounded support. -/
theorem parent_child_frozen_coordinate_support {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ minimumDepth : ℕ,
      ∀ (parent child : ℕ → Bool × Bool) (depth : ℕ), minimumDepth ≤ depth →
        (∀ index < depth, parent index = child index) → ∀ tail : ℕ → Bool × Bool,
        |parentFrozenCoordinate data parent child depth tail| ≤ radius ∧
        |childFrozenCoordinate data parent child depth tail| ≤ radius := by
  obtain ⟨parentRadius, parent_positive, parent_support⟩ := completeRootKernel_uniform_support data
  obtain ⟨childRadius, child_positive, minimumDepth, child_support⟩ := parent_child_kernel_common_support data
  refine ⟨parentRadius + childRadius, add_pos parent_positive child_positive, minimumDepth, ?_⟩
  intro parent child depth depth_ge agreement tail
  constructor
  · exact (parent_support parent (prependPairedDigit (child depth) tail) depth).trans
      (le_add_of_nonneg_right child_positive.le)
  · exact (child_support parent child tail depth depth_ge agreement).trans
      (le_add_of_nonneg_left parent_positive.le)

end LambdaCantor.First.Roots
