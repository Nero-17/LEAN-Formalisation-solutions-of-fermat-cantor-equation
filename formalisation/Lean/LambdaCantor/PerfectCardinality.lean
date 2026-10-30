import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Analysis.Real.Cardinality

noncomputable section
open scoped Cardinal
namespace LambdaCantor

/-- The standard perfect-set cardinality step, independent of the article's
construction of a nonempty perfect subset. -/
theorem cardinal_eq_continuum_of_perfect_subset
    {source target : Set (ℝ × ℝ)} (perfect : Perfect source)
    (nonempty : source.Nonempty) (contained : source ⊆ target) :
    Cardinal.mk target = Cardinal.continuum := by
  obtain ⟨encode, range_contained, _, injective⟩ :=
    perfect.exists_nat_bool_injection nonempty
  have lower : Cardinal.mk (ℕ → Bool) ≤ Cardinal.mk target := by
    apply Cardinal.mk_le_of_injective (f := fun digits =>
      (⟨encode digits, contained (range_contained ⟨digits, rfl⟩)⟩ : target))
    intro left right equal
    exact injective (congrArg Subtype.val equal)
  have upper := Cardinal.mk_set_le target
  have binary_cardinal : Cardinal.mk (ℕ → Bool) = Cardinal.continuum := by
    rw [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat,
      Cardinal.two_power_aleph0]
  rw [binary_cardinal] at lower
  have plane_cardinal : Cardinal.mk (ℝ × ℝ) = Cardinal.continuum := by
    simp [Cardinal.mk_prod, Cardinal.mk_real, Cardinal.continuum_mul_self]
  rw [plane_cardinal] at upper
  exact le_antisymm upper lower

end LambdaCantor
