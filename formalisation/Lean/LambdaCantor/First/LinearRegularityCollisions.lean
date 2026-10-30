import Mathlib.Tactic.Linarith
import LambdaCantor.Common
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
namespace LambdaCantor.First.LinearRegularity

/-- A graph that is C1 at every point of its parameter domain has Hausdorff
dimension at most one, even when the domain is not an interval. -/
theorem dimH_graph_le_one (domain : Set ℝ) (function : ℝ → ℝ)
    (hsmooth : ∀ point ∈ domain, ContDiffAt ℝ 1 function point) :
    dimH ((fun point => (point, function point)) '' domain) ≤ 1 := by
  have himage : dimH ((fun point => (point, function point)) '' domain) ≤ dimH domain := by
    apply dimH_image_le_of_locally_lipschitzOn
    intro point hpoint
    obtain ⟨constant, neighborhood, hneighborhood, hlipschitz⟩ :=
      (contDiffAt_id.prodMk (hsmooth point hpoint)).exists_lipschitzOnWith
    exact ⟨constant, neighborhood, mem_nhdsWithin_of_mem_nhds hneighborhood, hlipschitz⟩
  exact himage.trans ((dimH_mono (Set.subset_univ domain)).trans_eq Real.dimH_univ)

/-- Collisions of distinct affine-in-slope analytic block translations form
an at-most-one-dimensional set. The proof handles possible zeros of the
slope coefficient explicitly rather than presuming the quotient is smooth. -/
theorem dimH_affine_slope_collision_le_one (domain : Set ℝ)
    (slopeCoefficient intercept : ℝ → ℝ)
    (hslope : ∀ point ∈ domain, ContDiffAt ℝ 1 slopeCoefficient point)
    (hintercept : ∀ point ∈ domain, ContDiffAt ℝ 1 intercept point)
    (hnocommon : ∀ point ∈ domain, slopeCoefficient point ≠ 0 ∨ intercept point ≠ 0) :
    dimH {parameter : ℝ × ℝ | parameter.1 ∈ domain ∧
      parameter.2 * slopeCoefficient parameter.1 + intercept parameter.1 = 0} ≤ 1 := by
  have hsubset : {parameter : ℝ × ℝ | parameter.1 ∈ domain ∧
      parameter.2 * slopeCoefficient parameter.1 + intercept parameter.1 = 0} ⊆
      (fun point => (point, -intercept point / slopeCoefficient point)) ''
        {point ∈ domain | slopeCoefficient point ≠ 0} := by
    intro parameter hparameter
    change parameter.1 ∈ domain ∧
      parameter.2 * slopeCoefficient parameter.1 + intercept parameter.1 = 0 at hparameter
    have hnonzero : slopeCoefficient parameter.1 ≠ 0 := by
      rcases hnocommon parameter.1 hparameter.1 with hnonzero | hnonzero
      · exact hnonzero
      · intro hzero
        have hequation := hparameter.2
        rw [hzero, mul_zero, zero_add] at hequation
        exact hnonzero hequation
    refine ⟨parameter.1, ⟨hparameter.1, hnonzero⟩, ?_⟩
    apply Prod.ext
    · rfl
    change -intercept parameter.1 / slopeCoefficient parameter.1 = parameter.2
    apply (div_eq_iff hnonzero).mpr
    linarith [hparameter.2]
  apply (dimH_mono hsubset).trans
  apply dimH_graph_le_one
  intro point hpoint
  exact (hintercept point hpoint.1).neg.div (hslope point hpoint.1) hpoint.2

end LambdaCantor.First.LinearRegularity


