import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas

namespace LambdaCantor

/-- A unique zero of a jointly continuous residual varies continuously when
both the address space and the allowed root space are compact. -/
theorem continuous_unique_root
    {AddressSpace RootSpace : Type*}
    [TopologicalSpace AddressSpace] [CompactSpace AddressSpace] [T2Space AddressSpace]
    [TopologicalSpace RootSpace] [CompactSpace RootSpace]
    (residual : AddressSpace × RootSpace → ℝ)
    (hcontinuous : Continuous residual)
    (root : AddressSpace → RootSpace)
    (hroot : ∀ address, residual (address, root address) = 0)
    (hunique : ∀ address parameter, residual (address, parameter) = 0 →
      parameter = root address) : Continuous root := by
  let graph : Set (AddressSpace × RootSpace) := {point | residual point = 0}
  have hclosed : IsClosed graph := isClosed_eq hcontinuous continuous_const
  letI : CompactSpace graph := isCompact_iff_compactSpace.mp hclosed.isCompact
  let projection : graph ≃ AddressSpace :=
    { toFun := fun point => point.val.1
      invFun := fun address => ⟨(address, root address), hroot address⟩
      left_inv := by
        intro point
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact (hunique point.val.1 point.val.2 point.property).symm
      right_inv := by intro address; rfl }
  have hprojection : Continuous projection := continuous_fst.comp continuous_subtype_val
  have hinverse : Continuous projection.symm :=
    hprojection.continuous_symm_of_equiv_compact_to_t2
  exact continuous_snd.comp (continuous_subtype_val.comp hinverse)

end LambdaCantor
