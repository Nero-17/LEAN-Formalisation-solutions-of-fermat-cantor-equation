import LambdaCantor.Last.ReturnTree
import Mathlib.Data.Set.Countable

noncomputable section
namespace LambdaCantor.Last

/-- Cantor's diagonal argument for the binary branch space. -/
theorem uncountable_binaryBranches : Uncountable (ℕ → Bool) := by
  apply uncountable_iff_forall_not_surjective.mpr
  intro enumeration hsurjective
  obtain ⟨index, hindex⟩ := hsurjective (fun position => !(enumeration position position))
  have hdiagonal := congrFun hindex index
  cases hvalue : enumeration index index <;> simp [hvalue] at hdiagonal

/-- An injective binary coding forces every set containing its image to be uncountable. -/
theorem uncountable_of_injective_binary_coding {X : Type*}
    (coding : (ℕ → Bool) → X) (hinjective : Function.Injective coding)
    {target : Set X} (himage : ∀ branch, coding branch ∈ target) :
    ¬ target.Countable := by
  intro hcountable
  letI : Uncountable (ℕ → Bool) := uncountable_binaryBranches
  letI : Countable target := hcountable
  let restricted : (ℕ → Bool) → target := fun branch => ⟨coding branch, himage branch⟩
  have hinjectiveRestricted : Function.Injective restricted := by
    intro first second hequal
    exact hinjective (congrArg Subtype.val hequal)
  exact not_injective_uncountable_countable restricted hinjectiveRestricted

namespace CompactReturnTree
variable {X : Type*} [MetricSpace X] (tree : CompactReturnTree X)

/-- Eventual disjointness of distinct branch cylinders suffices for injectivity.
No uniform return-depth bound or quantitative dimension estimate is assumed. -/
theorem coding_injective_of_disjoint
    (hdisjoint : ∀ first second : ℕ → Bool, first ≠ second →
      ∃ depth, Disjoint (tree.cell first depth) (tree.cell second depth)) :
    Function.Injective tree.coding := by
  intro first second hequal
  by_contra hbranches
  obtain ⟨depth, hdepth⟩ := hdisjoint first second hbranches
  have hsecond := tree.coding_mem second depth
  rw [← hequal] at hsecond
  exact Set.disjoint_left.mp hdepth (tree.coding_mem first depth) hsecond

theorem uncountable_target_of_disjoint
    (hdisjoint : ∀ first second : ℕ → Bool, first ≠ second →
      ∃ depth, Disjoint (tree.cell first depth) (tree.cell second depth))
    {target : Set X} (himage : ∀ branch, tree.coding branch ∈ target) :
    ¬ target.Countable :=
  uncountable_of_injective_binary_coding tree.coding
    (tree.coding_injective_of_disjoint hdisjoint) himage

end CompactReturnTree
end LambdaCantor.Last
