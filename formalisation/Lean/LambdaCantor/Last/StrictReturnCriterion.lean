import LambdaCantor.Last.StrictReturnDimension
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

/-- The full robust strict-return criterion: a single perturbation threshold works
for every level in an open neighborhood of the original compact returning set.
The error needs to be Lipschitz only on the Cantor dust. -/
theorem strict_return_criterion (ratio : ℝ) (hpositive : 0 < ratio) (hless : ratio < 1 / 2)
    (linear : (ℝ × ℝ) →L[ℝ] ℝ) (levels : Set ℝ)
    (hcompact : IsCompact levels) (hnonempty : levels.Nonempty)
    (hreturns : ∀ level ∈ levels, ∃ pair : ReturnPair,
      linearWordReturn ratio linear.toLinearMap (pair.word false) level ∈ interior levels ∧
      linearWordReturn ratio linear.toLinearMap (pair.word true) level ∈ interior levels) :
    ∃ threshold : ℝ, 0 < threshold ∧ ∃ neighborhood : Set ℝ,
      IsOpen neighborhood ∧ levels ⊆ neighborhood ∧
      ∀ bound : ℝ≥0, (bound : ℝ) < threshold →
      ∀ error : (ℝ × ℝ) → ℝ, LipschitzOnWith bound error (cantorDust ratio) → error 0 = 0 →
      ∀ level ∈ neighborhood,
        0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧ linear point + error point = level} := by
  classical
  let returnDomain : Set ℝ := ⋃ pair : ReturnPair,
    (linearWordReturn ratio linear.toLinearMap (pair.word false)) ⁻¹' interior levels ∩
    (linearWordReturn ratio linear.toLinearMap (pair.word true)) ⁻¹' interior levels
  have hdomain_open : IsOpen returnDomain := isOpen_iUnion fun pair =>
    (isOpen_interior.preimage (continuous_linearWordReturn ratio linear.toLinearMap _)).inter
      (isOpen_interior.preimage (continuous_linearWordReturn ratio linear.toLinearMap _))
  have hdomain_contains : levels ⊆ returnDomain := by
    intro level hlevel
    obtain ⟨pair, hpair⟩ := hreturns level hlevel
    exact Set.mem_iUnion.mpr ⟨pair, hpair⟩
  obtain ⟨enlarged, henlarged_compact, hlevels_enlarged, henlarged_domain⟩ :=
    exists_compact_between hcompact hdomain_open hdomain_contains
  obtain ⟨levelBound, hlevelBound, hlevelBound_all⟩ :=
    henlarged_compact.isBounded.exists_pos_norm_le
  have henlarged_nonempty : enlarged.Nonempty :=
    hnonempty.mono (hlevels_enlarged.trans interior_subset)
  have henlarged_complement : enlargedᶜ.Nonempty := by
    refine ⟨levelBound + 1, ?_⟩
    intro hmem
    have hbound := hlevelBound_all _ hmem
    rw [Real.norm_eq_abs, abs_of_pos (by linarith)] at hbound
    linarith
  have henlarged_returns : ∀ level ∈ enlarged, ∃ pair : ReturnPair,
      linearWordReturn ratio linear.toLinearMap (pair.word false) level ∈ interior enlarged ∧
      linearWordReturn ratio linear.toLinearMap (pair.word true) level ∈ interior enlarged := by
    intro level hlevel
    obtain ⟨pair, hpair⟩ := Set.mem_iUnion.mp (henlarged_domain hlevel)
    exact ⟨pair, interior_mono (hlevels_enlarged.trans interior_subset) hpair.1,
      interior_mono (hlevels_enlarged.trans interior_subset) hpair.2⟩
  obtain ⟨atlas⟩ := exists_finiteReturnAtlas ratio linear.toLinearMap enlarged
    henlarged_compact henlarged_nonempty henlarged_complement henlarged_returns
  have hless_one : ratio < 1 := by linarith
  obtain ⟨linearBound, hlinearBound, hlinearBound_all⟩ :=
    ((isCompact_cantorDust hpositive.le hless_one).image linear.continuous).isBounded.exists_pos_norm_le
  refine ⟨atlas.margin * ratio ^ atlas.maxDepth,
    mul_pos atlas.margin_pos (pow_pos hpositive _), interior enlarged,
    isOpen_interior, hlevels_enlarged, ?_⟩
  intro bound hsmall error hlipschitz hzero level hlevel
  obtain ⟨extension, hextension, hagreement⟩ := hlipschitz.extend_real
  have hextension_zero : extension 0 = 0 := by
    rw [← hagreement ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩]
    exact hzero
  let initial : ReturnState enlarged bound :=
    ⟨level, interior_subset hlevel, extension, hextension_zero, hextension⟩
  have hlinear_abs : ∀ point ∈ cantorDust ratio, |linear point| ≤ linearBound := by
    intro point hpoint
    have hnorm := hlinearBound_all (linear point) ⟨point, hpoint, rfl⟩
    simpa only [Real.norm_eq_abs] using hnorm
  have hlevel_abs : ∀ value ∈ enlarged, |value| ≤ levelBound := by
    intro value hvalue
    simpa only [Real.norm_eq_abs] using hlevelBound_all value hvalue
  have hdimension := atlas.positive_dimension hpositive hless bound hsmall
    linearBound levelBound hlinearBound.le hlevelBound.le
    hlinear_abs hlevel_abs initial
  apply hdimension.trans_le (dimH_mono ?_)
  intro point hpoint
  refine ⟨hpoint.1, ?_⟩
  have hequation : linear point + extension point = level := hpoint.2
  rw [hagreement hpoint.1]
  exact hequation

end LambdaCantor.Last
