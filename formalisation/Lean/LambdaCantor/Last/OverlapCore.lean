import LambdaCantor.Last.TangentSource

noncomputable section
namespace LambdaCantor.Last

/-- The full closed image hull of a product child. -/
def affineChildHull (ratio slope : ℝ) (digit : Bool × Bool) : Set ℝ :=
  Set.Icc (positiveLinear slope (wordMap ratio [digit] 0))
    (positiveLinear slope (wordMap ratio [digit] 0) + ratio * (1 + slope))

/-- All pairwise overlaps are retained, including triple overlaps and endpoint
contacts. This is the compact core used by the analytic last-transition proof. -/
def affineOverlapCore (ratio slope : ℝ) : Set ℝ :=
  ⋃ pair : {pair : (Bool × Bool) × (Bool × Bool) // pair.1 ≠ pair.2},
    affineChildHull ratio slope pair.1.1 ∩ affineChildHull ratio slope pair.1.2

theorem isCompact_affineOverlapCore (ratio slope : ℝ) :
    IsCompact (affineOverlapCore ratio slope) := by
  apply isCompact_iUnion
  intro pair
  exact isCompact_Icc.inter isCompact_Icc

theorem mem_affineOverlapCore {ratio slope level : ℝ} :
    level ∈ affineOverlapCore ratio slope ↔
      ∃ first second : Bool × Bool, first ≠ second ∧
        level ∈ affineChildHull ratio slope first ∧
        level ∈ affineChildHull ratio slope second := by
  constructor
  · intro membership
    obtain ⟨pair, first_membership, second_membership⟩ := Set.mem_iUnion.mp membership
    exact ⟨pair.1.1, pair.1.2, pair.2, first_membership, second_membership⟩
  · rintro ⟨first, second, different, first_membership, second_membership⟩
    exact Set.mem_iUnion.mpr ⟨⟨(first, second), different⟩, first_membership, second_membership⟩

theorem positiveLinear_mem_unit_hull {ratio slope : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio < 1) (hslope : 0 ≤ slope)
    {point : ℝ × ℝ} (hpoint : point ∈ cantorDust ratio) :
    positiveLinear slope point ∈ Set.Icc 0 (1 + slope) := by
  obtain ⟨hfirst_nonnegative, hfirst_one⟩ := cantorSet_subset_unitInterval hratio hless hpoint.1
  obtain ⟨hsecond_nonnegative, hsecond_one⟩ := cantorSet_subset_unitInterval hratio hless hpoint.2
  change 0 ≤ point.1 + slope * point.2 ∧ point.1 + slope * point.2 ≤ 1 + slope
  constructor
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_left hsecond_one hslope]

theorem positiveLinear_child_mem_hull {ratio slope : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio < 1) (hslope : 0 ≤ slope)
    (digit : Bool × Bool) {point : ℝ × ℝ} (hpoint : point ∈ cantorDust ratio) :
    positiveLinear slope (wordMap ratio [digit] point) ∈ affineChildHull ratio slope digit := by
  have hlevel := positiveLinear_mem_unit_hull hratio hless hslope hpoint
  rw [wordMap_affine ratio [digit] point]
  simp only [map_add, map_smul, List.length_singleton, pow_one, smul_eq_mul]
  change positiveLinear slope (wordMap ratio [digit] 0) ≤
      positiveLinear slope (wordMap ratio [digit] 0) + ratio * positiveLinear slope point ∧
    positiveLinear slope (wordMap ratio [digit] 0) + ratio * positiveLinear slope point ≤
      positiveLinear slope (wordMap ratio [digit] 0) + ratio * (1 + slope)
  constructor <;> nlinarith [mul_nonneg hratio hlevel.1,
    mul_le_mul_of_nonneg_left hlevel.2 hratio]

/-- A local open-neighborhood estimate for the intersection of two real hulls.
Empty intersections are covered as well: sufficiently small simultaneous
endpoint errors are then impossible. -/
theorem approximate_interval_intersection_mem_open
    (firstLower firstUpper secondLower secondUpper : ℝ)
    (neighborhood : Set ℝ) (hopen : IsOpen neighborhood)
    (hcontains : Set.Icc firstLower firstUpper ∩ Set.Icc secondLower secondUpper ⊆ neighborhood) :
    ∃ margin : ℝ, 0 < margin ∧ ∀ error level : ℝ,
      error < margin → firstLower - error ≤ level → level ≤ firstUpper + error →
      secondLower - error ≤ level → level ≤ secondUpper + error → level ∈ neighborhood := by
  by_cases horder : max firstLower secondLower ≤ min firstUpper secondUpper
  · obtain ⟨margin, hmargin, hmargin_mem⟩ := open_interval_neighborhood_margin horder hopen (by
      intro level membership
      apply hcontains
      exact ⟨⟨(le_max_left _ _).trans membership.1,
        membership.2.trans (min_le_left _ _)⟩,
        ⟨(le_max_right _ _).trans membership.1,
        membership.2.trans (min_le_right _ _)⟩⟩)
    refine ⟨margin, hmargin, ?_⟩
    intro error level herror hfirstLower hfirstUpper hsecondLower hsecondUpper
    apply hmargin_mem
    · rcases le_total firstLower secondLower with comparison | comparison
      · rw [max_eq_right comparison]
        linarith
      · rw [max_eq_left comparison]
        linarith
    · rcases le_total firstUpper secondUpper with comparison | comparison
      · rw [min_eq_left comparison]
        linarith
      · rw [min_eq_right comparison]
        linarith
  · refine ⟨(max firstLower secondLower - min firstUpper secondUpper) / 2, by linarith, ?_⟩
    intro error level herror hfirstLower hfirstUpper hsecondLower hsecondUpper
    have hlower : max firstLower secondLower - error ≤ level := by
      rcases le_total firstLower secondLower with comparison | comparison
      · rwa [max_eq_right comparison]
      · rwa [max_eq_left comparison]
    have hupper : level ≤ min firstUpper secondUpper + error := by
      rcases le_total firstUpper secondUpper with comparison | comparison
      · rwa [min_eq_left comparison]
      · rwa [min_eq_right comparison]
    exfalso
    linarith

end LambdaCantor.Last
