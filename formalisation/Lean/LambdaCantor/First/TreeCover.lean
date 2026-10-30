import LambdaCantor.First.ExceptionalSlopes

noncomputable section
namespace LambdaCantor.First

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- Iterating a bound on active children bounds each finite level. -/
theorem active_level_card_le_pow {Index : ℕ → Type*}
    [∀ level, DecidableEq (Index level)]
    (active : (level : ℕ) → Finset (Index level))
    (parent : (level : ℕ) → Index (level + 1) → Index level)
    (branching : ℕ) (hroot : (active 0).card ≤ 1)
    (hparent : ∀ level, Set.MapsTo (parent level) (↑(active (level + 1))) (↑(active level)))
    (hchildren : ∀ level index, index ∈ active level →
      ((active (level + 1)).filter (fun child => parent level child = index)).card ≤ branching) :
    ∀ level, (active level).card ≤ branching ^ level := by
  intro level
  induction level with
  | zero => simpa only [pow_zero] using hroot
  | succ level hinduction =>
    calc
      (active (level + 1)).card = ∑ index ∈ active level,
          ((active (level + 1)).filter (fun child => parent level child = index)).card :=
        Finset.card_eq_sum_card_fiberwise (hparent level)
      _ ≤ ∑ _index ∈ active level, branching := Finset.sum_le_sum (hchildren level)
      _ = (active level).card * branching := by simp
      _ ≤ branching ^ level * branching := Nat.mul_le_mul_right branching hinduction
      _ = branching ^ (level + 1) := (pow_succ _ _).symm

/-- A recursive geometric cover with uniformly bounded active branching has
the expected Hausdorff bound. All hypotheses concern finite parent/child
counts and diameters, rather than any dimension conclusion. -/
theorem dimH_le_of_active_tree {X : Type*} [EMetricSpace X]
    {Index : ℕ → Type*} [∀ level, DecidableEq (Index level)]
    (active : (level : ℕ) → Finset (Index level))
    (parent : (level : ℕ) → Index (level + 1) → Index level)
    (branching : ℕ) (hroot : (active 0).card ≤ 1)
    (hparent : ∀ level, Set.MapsTo (parent level) (↑(active (level + 1))) (↑(active level)))
    (hchildren : ∀ level index, index ∈ active level →
      ((active (level + 1)).filter (fun child => parent level child = index)).card ≤ branching)
    {s : Set X} {ratio constant : ℝ≥0∞} (hsmall : ratio < 1) (hconstant : constant ≠ ∞)
    (exponent : ℝ≥0) (hcost : (branching : ℝ≥0∞) * ratio ^ (exponent : ℝ) < 1)
    (cover : (level : ℕ) → Index level → Set X)
    (hdiam : ∀ level index, index ∈ active level →
      Metric.ediam (cover level index) ≤ constant * ratio ^ level)
    (hcover : ∀ level, s ⊆ ⋃ index ∈ active level, cover level index) :
    dimH s ≤ exponent := by
  apply ExceptionalSlopes.dimH_le_of_scaled_geometric_tail_covers
    (Index := fun level => {index // index ∈ active level}) hsmall hconstant exponent
    (branching := (branching : ℝ≥0∞))
    (cover := fun level index => cover level index.val)
  · intro level
    have h := active_level_card_le_pow active parent branching hroot hparent hchildren level
    simpa only [Fintype.card_coe, Nat.cast_pow] using
      (show ((active level).card : ℝ≥0∞) ≤ (branching ^ level : ℕ) by exact_mod_cast h)
  · exact hcost
  · intro level index
    exact hdiam level index.val index.property
  · intro first point hpoint
    obtain ⟨index, hindex, hmem⟩ := Set.mem_iUnion₂.1 (hcover first hpoint)
    exact Set.mem_iUnion₂.2 ⟨first, le_rfl,
      Set.mem_iUnion.2 ⟨⟨index, hindex⟩, hmem⟩⟩

end LambdaCantor.First
