import LambdaCantor.Last.ReturnParameterPersistence
import LambdaCantor.Last.StrictReturnCriterion

noncomputable section
open Filter
open scoped NNReal Topology
namespace LambdaCantor.Last

/-- A single error threshold and a fixed level neighborhood work for every
nearby contraction. The finite return words and their margin are retained;
no perfect set is assumed at a perturbed contraction. -/
theorem strict_return_criterion_persist_parameter {ratio : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2)
    (linear : (ℝ × ℝ) →L[ℝ] ℝ) (levels : Set ℝ)
    (compact : IsCompact levels) (nonempty : levels.Nonempty)
    (returns : ∀ level ∈ levels, ∃ pair : ReturnPair,
      linearWordReturn ratio linear.toLinearMap (pair.word false) level ∈ interior levels ∧
      linearWordReturn ratio linear.toLinearMap (pair.word true) level ∈ interior levels) :
    ∃ threshold : ℝ, 0 < threshold ∧ ∃ neighborhood : Set ℝ,
      IsOpen neighborhood ∧ levels ⊆ neighborhood ∧
      ∀ᶠ perturbed in 𝓝 ratio, 0 < perturbed ∧ perturbed < 1/2 ∧
        ∀ bound : ℝ≥0, (bound : ℝ) < threshold →
        ∀ error : (ℝ × ℝ) → ℝ, LipschitzOnWith bound error (cantorDust perturbed) →
          error 0 = 0 → ∀ level ∈ neighborhood,
          0 < dimH {point | point ∈ cantorDust perturbed ∧ linear point+error point = level} := by
  classical
  let returnDomain : Set ℝ := ⋃ pair : ReturnPair,
    (linearWordReturn ratio linear.toLinearMap (pair.word false)) ⁻¹' interior levels ∩
      (linearWordReturn ratio linear.toLinearMap (pair.word true)) ⁻¹' interior levels
  have domain_open : IsOpen returnDomain := isOpen_iUnion fun pair =>
    (isOpen_interior.preimage (continuous_linearWordReturn ratio linear.toLinearMap _)).inter
      (isOpen_interior.preimage (continuous_linearWordReturn ratio linear.toLinearMap _))
  have domain_contains : levels ⊆ returnDomain := by
    intro level membership
    obtain ⟨pair, pair_returns⟩ := returns level membership
    exact Set.mem_iUnion.mpr ⟨pair, pair_returns⟩
  obtain ⟨enlarged, enlarged_compact, enlarged_contains, enlarged_domain⟩ :=
    exists_compact_between compact domain_open domain_contains
  have enlarged_nonempty : enlarged.Nonempty :=
    nonempty.mono (enlarged_contains.trans interior_subset)
  obtain ⟨levelBound, levelBound_positive, levelBound_all⟩ :=
    enlarged_compact.isBounded.exists_pos_norm_le
  have enlarged_complement : enlargedᶜ.Nonempty := by
    refine ⟨levelBound+1, ?_⟩
    intro membership
    have bound := levelBound_all _ membership
    rw [Real.norm_eq_abs, abs_of_pos (by linarith)] at bound
    linarith
  have enlarged_returns : ∀ level ∈ enlarged, ∃ pair : ReturnPair,
      linearWordReturn ratio linear.toLinearMap (pair.word false) level ∈ interior enlarged ∧
      linearWordReturn ratio linear.toLinearMap (pair.word true) level ∈ interior enlarged := by
    intro level membership
    obtain ⟨pair, pair_returns⟩ := Set.mem_iUnion.mp (enlarged_domain membership)
    exact ⟨pair, interior_mono (enlarged_contains.trans interior_subset) pair_returns.1,
      interior_mono (enlarged_contains.trans interior_subset) pair_returns.2⟩
  obtain ⟨selected, margin, margin_positive, persistent⟩ :=
    compact_strict_returns_persist_parameter positive.ne' linear enlarged enlarged_compact
      enlarged_nonempty enlarged_complement enlarged_returns
  let maximumDepth := selected.sup (fun pair => max (pair.word false).length (pair.word true).length)
  refine ⟨margin*(ratio/2)^maximumDepth, mul_pos margin_positive (pow_pos (half_pos positive) _),
    interior enlarged, isOpen_interior, enlarged_contains, ?_⟩
  filter_upwards [persistent, lt_mem_nhds (show ratio/2 < ratio by linarith),
    gt_mem_nhds less_half] with perturbed perturbed_returns lower upper
  have perturbed_positive : 0 < perturbed := (half_pos positive).trans lower
  have perturbed_less_one : perturbed < 1 := by linarith
  refine ⟨perturbed_positive, upper, ?_⟩
  intro bound bound_small error lipschitz error_zero level level_mem
  let chosen : enlarged → ReturnPair := fun value => (perturbed_returns value value.property).choose
  have chosen_mem (value : enlarged) : chosen value ∈ selected :=
    (perturbed_returns value value.property).choose_spec.1
  let atlas : FiniteReturnAtlas perturbed linear.toLinearMap enlarged := {
    pair := chosen
    maxDepth := maximumDepth
    length_le := by
      intro value bit
      have bound := Finset.le_sup (f := fun pair : ReturnPair =>
        max (pair.word false).length (pair.word true).length) (chosen_mem value)
      cases bit
      · exact (le_max_left _ _).trans bound
      · exact (le_max_right _ _).trans bound
    margin := margin
    margin_pos := margin_positive
    robust := by
      intro value values values_close bit
      have result := (perturbed_returns value value.property).choose_spec.2
        (values false) (values true) (values_close false) (values_close true)
      cases bit
      · exact result.1
      · exact result.2 }
  have uniform_small : (bound : ℝ) < atlas.margin*perturbed^atlas.maxDepth := by
    apply bound_small.trans_le
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (half_pos positive).le lower.le maximumDepth) margin_positive.le
  obtain ⟨extension, extension_lipschitz, agreement⟩ := lipschitz.extend_real
  have extension_zero : extension 0 = 0 := by
    rw [← agreement ⟨zero_mem_cantorSet perturbed, zero_mem_cantorSet perturbed⟩]
    exact error_zero
  let initial : ReturnState enlarged bound :=
    ⟨level, interior_subset level_mem, extension, extension_zero, extension_lipschitz⟩
  obtain ⟨linearBound, linearBound_positive, linearBound_all⟩ :=
    ((isCompact_cantorDust perturbed_positive.le perturbed_less_one).image linear.continuous).isBounded.exists_pos_norm_le
  have linear_abs : ∀ point ∈ cantorDust perturbed, |linear point| ≤ linearBound := by
    intro point membership
    simpa only [Real.norm_eq_abs] using linearBound_all (linear point) ⟨point, membership, rfl⟩
  have dimension := atlas.positive_dimension perturbed_positive upper bound uniform_small
    linearBound levelBound linearBound_positive.le levelBound_positive.le
    linear_abs
    (fun value membership => by
      simpa only [Real.norm_eq_abs] using levelBound_all value membership) initial
  apply dimension.trans_le (dimH_mono ?_)
  intro point membership
  refine ⟨membership.1, ?_⟩
  have equation : linear point+extension point = level := membership.2
  rw [agreement membership.1]
  exact equation

end LambdaCantor.Last
