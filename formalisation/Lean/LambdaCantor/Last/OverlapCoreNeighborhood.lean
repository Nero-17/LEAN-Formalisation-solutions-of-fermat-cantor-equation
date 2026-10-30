import LambdaCantor.Last.OverlapCore
import Mathlib.Tactic.Choose

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

/-- A single error margin works for every pair of child hulls. The core is
the union of every closed pairwise intersection, so no ordering or exclusion
of triple overlaps enters this statement. -/
theorem affineOverlapCore_neighborhood_margin
    (ratio slope : ℝ) (neighborhood : Set ℝ) (hopen : IsOpen neighborhood)
    (hcontains : affineOverlapCore ratio slope ⊆ neighborhood) :
    ∃ margin : ℝ, 0 < margin ∧ ∀ error level : ℝ, error < margin →
      ∀ first second : Bool × Bool, first ≠ second →
      positiveLinear slope (wordMap ratio [first] 0) - error ≤ level →
      level ≤ positiveLinear slope (wordMap ratio [first] 0) + ratio * (1 + slope) + error →
      positiveLinear slope (wordMap ratio [second] 0) - error ≤ level →
      level ≤ positiveLinear slope (wordMap ratio [second] 0) + ratio * (1 + slope) + error →
      level ∈ neighborhood := by
  have pair_margins : ∀ pair : {pair : (Bool × Bool) × (Bool × Bool) // pair.1 ≠ pair.2},
      ∃ margin : ℝ, 0 < margin ∧ ∀ error level : ℝ, error < margin →
        positiveLinear slope (wordMap ratio [pair.1.1] 0) - error ≤ level →
        level ≤ positiveLinear slope (wordMap ratio [pair.1.1] 0) + ratio * (1 + slope) + error →
        positiveLinear slope (wordMap ratio [pair.1.2] 0) - error ≤ level →
        level ≤ positiveLinear slope (wordMap ratio [pair.1.2] 0) + ratio * (1 + slope) + error →
        level ∈ neighborhood := by
    intro pair
    apply approximate_interval_intersection_mem_open _ _ _ _ neighborhood hopen
    intro level membership
    apply hcontains
    apply mem_affineOverlapCore.mpr
    exact ⟨pair.1.1, pair.1.2, pair.2, membership.1, membership.2⟩
  choose margins positive controls using pair_margins
  have common : ∀ᶠ margin : ℝ in 𝓝 0, ∀ pair, margin < margins pair := by
    apply Filter.eventually_all.mpr
    intro pair
    exact gt_mem_nhds (positive pair)
  have positive_event : ∀ᶠ value : ℝ in 𝓝[>] (0 : ℝ), 0 < value := self_mem_nhdsWithin
  obtain ⟨margin, hmargin, hcommon⟩ :=
    (positive_event.and (common.filter_mono nhdsWithin_le_nhds)).exists
  refine ⟨margin, hmargin, ?_⟩
  intro error level herror first second different hfirstLower hfirstUpper hsecondLower hsecondUpper
  exact controls ⟨(first, second), different⟩ error level
    (herror.trans (hcommon ⟨(first, second), different⟩))
    hfirstLower hfirstUpper hsecondLower hsecondUpper

theorem perturbed_child_level_bounds {ratio slope bound level : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio < 1) (hslope : 0 ≤ slope)
    (error : (ℝ × ℝ) → ℝ)
    (herror : ∀ point ∈ cantorDust ratio, |error point| ≤ bound)
    (digit : Bool × Bool) {point : ℝ × ℝ} (hpoint : point ∈ cantorDust ratio)
    (hlevel : positiveLinear slope (wordMap ratio [digit] point) +
      error (wordMap ratio [digit] point) = level) :
    positiveLinear slope (wordMap ratio [digit] 0) - bound ≤ level ∧
      level ≤ positiveLinear slope (wordMap ratio [digit] 0) + ratio * (1 + slope) + bound := by
  have hhull := positiveLinear_child_mem_hull hratio hless hslope digit hpoint
  have herror_bound := abs_le.mp (herror _ (wordMap_mem_dust hratio hless [digit] hpoint))
  change positiveLinear slope (wordMap ratio [digit] 0) ≤
      positiveLinear slope (wordMap ratio [digit] point) ∧
    positiveLinear slope (wordMap ratio [digit] point) ≤
      positiveLinear slope (wordMap ratio [digit] 0) + ratio * (1 + slope) at hhull
  constructor <;> linarith [hhull.1, hhull.2, herror_bound.1, herror_bound.2]

end LambdaCantor.Last
