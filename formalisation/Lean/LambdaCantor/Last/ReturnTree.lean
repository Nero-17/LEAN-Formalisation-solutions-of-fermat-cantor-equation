import LambdaCantor.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

noncomputable section
open Filter Set
open scoped Topology
namespace LambdaCantor.Last

/-- A binary tree of nested compact cells, indexed by branches. The finite-prefix
condition is explicit, so this structure does not assume any limiting coding map. -/
structure CompactReturnTree (X : Type*) [MetricSpace X] where
  cell : (ℕ → Bool) → ℕ → Set X
  nonempty : ∀ branch depth, (cell branch depth).Nonempty
  compact : ∀ branch depth, IsCompact (cell branch depth)
  nested : ∀ branch depth, cell branch (depth + 1) ⊆ cell branch depth
  prefix_agreement : ∀ first second depth,
    (∀ position < depth, first position = second position) →
    cell first depth = cell second depth
  diameterBound : ℕ → ℝ
  bound_tendsto : Tendsto diameterBound atTop (𝓝 0)
  dist_bound : ∀ branch depth, ∀ x ∈ cell branch depth,
    ∀ y ∈ cell branch depth, dist x y ≤ diameterBound depth

namespace CompactReturnTree
variable {X : Type*} [MetricSpace X] (tree : CompactReturnTree X)

theorem branch_nonempty (branch : ℕ → Bool) :
    (⋂ depth, tree.cell branch depth).Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (tree.cell branch) (tree.nested branch) (tree.nonempty branch)
    (tree.compact branch 0) (fun depth => (tree.compact branch depth).isClosed)

/-- The point obtained from the nested compact intersections. -/
def coding (branch : ℕ → Bool) : X := (tree.branch_nonempty branch).choose

theorem coding_mem (branch : ℕ → Bool) (depth : ℕ) :
    tree.coding branch ∈ tree.cell branch depth :=
  Set.mem_iInter.mp (tree.branch_nonempty branch).choose_spec depth

theorem coding_dist_le_of_prefix (first second : ℕ → Bool) (depth : ℕ)
    (agreement : ∀ position < depth, first position = second position) :
    dist (tree.coding first) (tree.coding second) ≤ tree.diameterBound depth := by
  apply tree.dist_bound first depth _ (tree.coding_mem first depth)
  rw [tree.prefix_agreement first second depth agreement]
  exact tree.coding_mem second depth

theorem continuous_coding : Continuous tree.coding := by
  apply continuous_iff_continuousAt.mpr
  intro first
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  obtain ⟨depth, hdepth⟩ := ((tree.bound_tendsto.eventually
    (gt_mem_nhds hepsilon)).exists)
  have agreement : ∀ᶠ second in 𝓝 first,
      ∀ position ∈ Finset.range depth, second position = first position := by
    rw [Filter.eventually_all_finset]
    intro position hposition
    exact (continuous_apply position).continuousAt.preimage_mem_nhds
      ((isOpen_discrete _).mem_nhds (Set.mem_singleton (first position)))
  filter_upwards [agreement] with second hsecond
  exact (tree.coding_dist_le_of_prefix second first depth
    (fun position hposition => hsecond position (Finset.mem_range.mpr hposition))).trans_lt hdepth

/-- Membership of every cell in a fixed target set passes to the coding image. -/
theorem range_coding_subset {target : Set X}
    (contained : ∀ branch, tree.cell branch 0 ⊆ target) :
    Set.range tree.coding ⊆ target := by
  rintro point ⟨branch, rfl⟩
  exact contained branch (tree.coding_mem branch 0)

/-- The normalized residual estimate suffices for exact zero-set membership. -/
theorem coding_level (function : X → ℝ) (level : ℝ)
    (residualBound : ℕ → ℝ) (hbound : Tendsto residualBound atTop (𝓝 0))
    (residual : ∀ branch depth, ∀ point ∈ tree.cell branch depth,
      |function point - level| ≤ residualBound depth) (branch : ℕ → Bool) :
    function (tree.coding branch) = level := by
  have hle : |function (tree.coding branch) - level| ≤ 0 :=
    ge_of_tendsto' hbound (fun depth => residual branch depth _ (tree.coding_mem branch depth))
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))

/-- Separation is checked on finite cylinders, then inherited by the limit map. -/
theorem tendsto_of_mem_cells (branch : ℕ → Bool) (points : ℕ → X)
    (hpoints : ∀ depth, points depth ∈ tree.cell branch depth) :
    Tendsto points atTop (𝓝 (tree.coding branch)) := by
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  obtain ⟨depth, hdepth⟩ := Filter.eventually_atTop.mp
    (tree.bound_tendsto.eventually (gt_mem_nhds hepsilon))
  refine ⟨depth, fun later hlater => ?_⟩
  exact (tree.dist_bound branch later _ (hpoints later) _
    (tree.coding_mem branch later)).trans_lt (hdepth later hlater)

/-- Corner values bracketing a level force that exact level at the limiting point. -/
theorem coding_level_of_brackets (function : X → ℝ) (level : ℝ)
    (branch : ℕ → Bool) (hcontinuous : ContinuousAt function (tree.coding branch))
    (lower upper : ℕ → X)
    (hlower_mem : ∀ depth, lower depth ∈ tree.cell branch depth)
    (hupper_mem : ∀ depth, upper depth ∈ tree.cell branch depth)
    (hlower : ∀ depth, function (lower depth) ≤ level)
    (hupper : ∀ depth, level ≤ function (upper depth)) :
    function (tree.coding branch) = level := by
  apply le_antisymm
  · exact le_of_tendsto' (hcontinuous.tendsto.comp
      (tree.tendsto_of_mem_cells branch lower hlower_mem)) hlower
  · exact ge_of_tendsto' (hcontinuous.tendsto.comp
      (tree.tendsto_of_mem_cells branch upper hupper_mem)) hupper

/-- Separation is checked on finite cylinders, then inherited by the limit map. -/
theorem coding_separated (depth : ℕ) (separation : ℝ)
    (separated : ∀ first second : ℕ → Bool,
      (∃ position < depth, first position ≠ second position) →
      ∀ x ∈ tree.cell first depth, ∀ y ∈ tree.cell second depth,
        separation ≤ dist x y)
    (first second : ℕ → Bool)
    (different : ∃ position < depth, first position ≠ second position) :
    separation ≤ dist (tree.coding first) (tree.coding second) :=
  separated first second different _ (tree.coding_mem first depth)
    _ (tree.coding_mem second depth)

end CompactReturnTree
end LambdaCantor.Last
