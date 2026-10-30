import LambdaCantor.First.RootsKernelPair

noncomputable section
namespace LambdaCantor.First.Roots

theorem completeRootKernel_affine_model {exponent : ℝ} (data : RootFibreData exponent)
    (representative : ℕ → Bool × Bool) (depth : ℕ) :
    ∃ center : ℝ, ∀ tail : ℕ → Bool × Bool,
      completeRootKernel data representative depth tail =
        center - rootKernelVertical data representative depth * projectedRootModel (rootFibreState data representative) tail := by
  refine ⟨data.root representative + rootKernelHorizontal data representative depth *
      address (data.root representative) (fun index => (representative (index + depth)).1) +
      rootKernelVertical data representative depth *
      address (data.root representative) (fun index => (representative (index + depth)).2), ?_⟩
  intro tail
  rw [completeRootKernel_formula]
  change data.root representative - rootKernelHorizontal data representative depth *
      (address (data.root representative) (fun index => (tail index).1) -
        address (data.root representative) (fun index => (representative (index + depth)).1)) -
      rootKernelVertical data representative depth *
      (address (data.root representative) (fun index => (tail index).2) -
        address (data.root representative) (fun index => (representative (index + depth)).2)) =
    data.root representative + rootKernelHorizontal data representative depth *
      address (data.root representative) (fun index => (representative (index + depth)).1) +
      rootKernelVertical data representative depth *
      address (data.root representative) (fun index => (representative (index + depth)).2) -
      rootKernelVertical data representative depth *
        ((rootFibreState data representative).2 * address (data.root representative) (fun index => (tail index).1) +
          address (data.root representative) (fun index => (tail index).2))
  rw [← rootKernel_coefficient_ratio data representative depth]
  field_simp [rootKernelVertical_ne_zero data representative depth]
  <;> ring

theorem projectedRootModel_prepend {parameter : ℝ × ℝ} (nonnegative : 0 ≤ parameter.1)
    (less_one : parameter.1 < 1) (digit : Bool × Bool) (tail : ℕ → Bool × Bool) :
    projectedRootModel parameter (prependPairedDigit digit tail) =
      (1 - parameter.1) * (parameter.2 * (if digit.1 then 1 else 0) + (if digit.2 then 1 else 0)) +
        parameter.1 * projectedRootModel parameter tail := by
  have first : (fun index => (prependPairedDigit digit tail index).1) =
      prependDigit digit.1 (fun index => (tail index).1) := by
    funext index
    cases index <;> simp [prependPairedDigit, prependDigit]
  have second : (fun index => (prependPairedDigit digit tail index).2) =
      prependDigit digit.2 (fun index => (tail index).2) := by
    funext index
    cases index <;> simp [prependPairedDigit, prependDigit]
  unfold projectedRootModel
  rw [first, second, address_prepend nonnegative less_one, address_prepend nonnegative less_one]
  ring

/-- Both laws in a genuine replacement are affine images of their actual
state laws, with the parent branch's additional first-digit contraction. -/
theorem parent_child_frozen_coordinate_models {exponent : ℝ} (data : RootFibreData exponent)
    (parent child : ℕ → Bool × Bool) (depth : ℕ) :
    (∃ center : ℝ, ∀ tail : ℕ → Bool × Bool,
      parentFrozenCoordinate data parent child depth tail = center +
        (-rootKernelVertical data parent depth * data.root parent / data.root parent ^ depth) *
          projectedRootModel (rootFibreState data parent) tail) ∧
    (∃ center : ℝ, ∀ tail : ℕ → Bool × Bool,
      childFrozenCoordinate data parent child depth tail = center +
        (-rootKernelVertical data child (depth + 1) / data.root parent ^ depth) *
          projectedRootModel (rootFibreState data child) tail) := by
  obtain ⟨parentCenter, parent_model⟩ := completeRootKernel_affine_model data parent depth
  obtain ⟨childCenter, child_model⟩ := completeRootKernel_affine_model data child (depth + 1)
  have ratio_nonnegative : 0 ≤ (rootFibreState data parent).1 := by
    change 0 ≤ data.root parent
    linarith [data.lower_gt_quarter, (data.root_in_band parent).1]
  have ratio_less : (rootFibreState data parent).1 < 1 := by
    change data.root parent < 1
    linarith [data.upper_lt_half, (data.root_in_band parent).2]
  constructor
  · refine ⟨(parentCenter - rootKernelVertical data parent depth *
      ((1 - data.root parent) * ((rootFibreState data parent).2 * (if (child depth).1 then 1 else 0) +
        (if (child depth).2 then 1 else 0))) - data.root parent) / data.root parent ^ depth, ?_⟩
    intro tail
    unfold parentFrozenCoordinate
    rw [parent_model, projectedRootModel_prepend ratio_nonnegative ratio_less]
    change (parentCenter - rootKernelVertical data parent depth *
      ((1 - data.root parent) * ((rootFibreState data parent).2 * (if (child depth).1 then 1 else 0) +
        (if (child depth).2 then 1 else 0)) + data.root parent *
          projectedRootModel (rootFibreState data parent) tail) - data.root parent) / data.root parent ^ depth = _
    ring
  · refine ⟨(childCenter - data.root parent) / data.root parent ^ depth, ?_⟩
    intro tail
    unfold childFrozenCoordinate
    rw [child_model]
    ring

end LambdaCantor.First.Roots
