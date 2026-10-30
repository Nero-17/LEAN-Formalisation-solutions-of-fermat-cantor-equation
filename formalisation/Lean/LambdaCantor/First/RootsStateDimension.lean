import LambdaCantor.First.RootsStateInverse
import Mathlib.Topology.MetricSpace.HausdorffDimension

noncomputable section
namespace LambdaCantor.First.Roots

open Set
open scoped NNReal

def positiveCurvePatch (exponent parameterLower parameterUpper coordinateLower : ℝ) :
    Set (ℝ × ℝ × ℝ) :=
  (Set.Icc parameterLower parameterUpper).prod
    ((Set.Icc coordinateLower 1).prod (Set.Icc coordinateLower 1)) ∩
      {point | point.2.1 ^ exponent + point.2.2 ^ exponent = 1}

theorem incidenceState_antilipschitz_on_patch
    {exponent shift parameterLower parameterUpper coordinateLower : ℝ}
    (hexponent : 1 < exponent) (hparameter : 0 < parameterLower)
    (hcoordinate : 0 < coordinateLower) :
    ∃ constant : ℝ≥0, AntilipschitzWith constant
      (fun point : positiveCurvePatch exponent parameterLower parameterUpper coordinateLower =>
        incidenceState exponent shift point.val) := by
  obtain ⟨constant, hconstant⟩ := incidenceState_inverse_bound
    (shift := shift) (parameterUpper := parameterUpper) hexponent hparameter hcoordinate
  refine ⟨constant, AntilipschitzWith.of_le_mul_dist ?_⟩
  intro left right
  exact hconstant left.val left.property.1 right.val right.property.1
    left.property.2 right.property.2

/-- A state exceptional set pulls back to an incidence exceptional set of
no greater Hausdorff dimension on every positive compact curve patch. -/
theorem incidenceState_preimage_dimension
    {exponent shift parameterLower parameterUpper coordinateLower : ℝ}
    (hexponent : 1 < exponent) (hparameter : 0 < parameterLower)
    (hcoordinate : 0 < coordinateLower) (exceptional : Set (ℝ × ℝ)) :
    dimH (positiveCurvePatch exponent parameterLower parameterUpper coordinateLower ∩
      incidenceState exponent shift ⁻¹' exceptional) ≤ dimH exceptional := by
  obtain ⟨constant, hconstant⟩ := incidenceState_antilipschitz_on_patch
    (shift := shift) (parameterUpper := parameterUpper) hexponent hparameter hcoordinate
  have hbound := hconstant.dimH_preimage_le exceptional
  have hequal : (Subtype.val ''
      ((fun point : positiveCurvePatch exponent parameterLower parameterUpper coordinateLower =>
        incidenceState exponent shift point.val) ⁻¹' exceptional)) =
      positiveCurvePatch exponent parameterLower parameterUpper coordinateLower ∩
        incidenceState exponent shift ⁻¹' exceptional := by
    ext point
    constructor
    · rintro ⟨point, hpoint, rfl⟩
      exact ⟨point.property, hpoint⟩
    · rintro ⟨hpatch, hpoint⟩
      exact ⟨⟨point, hpatch⟩, hpoint, rfl⟩
  rw [← hequal, isometry_subtype_coe.dimH_image]
  exact hbound

end LambdaCantor.First.Roots
