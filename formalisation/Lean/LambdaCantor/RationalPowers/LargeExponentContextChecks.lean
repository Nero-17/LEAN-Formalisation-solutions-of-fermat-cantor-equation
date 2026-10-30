import LambdaCantor.Integer.FinitePhaseChecker

namespace LambdaCantor.RationalPowers
open Integer

/-- The exact fields on which the logarithmic phase cache depends.
Coefficient bounds and their common grid denominator are deliberately absent. -/
def LargeExponentSamePhaseContext (first second : FinitePhaseCell) : Prop :=
  first.m = second.m ∧ first.endpointDepth = second.endpointDepth ∧
  first.height = second.height ∧ first.verticalDepth = second.verticalDepth ∧
  first.endpoint = second.endpoint

instance (first second : FinitePhaseCell) : Decidable (LargeExponentSamePhaseContext first second) := by
  unfold LargeExponentSamePhaseContext
  infer_instance

theorem largeExponent_same_phase_cache (first second : FinitePhaseCell)
    (same : LargeExponentSamePhaseContext first second) (geometry : TailPhaseGeometry) :
    finitePhaseCache first geometry = finitePhaseCache second geometry := by
  rcases same with ⟨layer,endpoint_depth,height,vertical_depth,endpoint⟩
  simp only [finitePhaseCache,finitePhaseOffsetInterval,finitePhaseCenter,finitePhaseLength,
    layer,endpoint_depth,height,vertical_depth,endpoint]

theorem largeExponent_same_phase_analytic (first second : FinitePhaseCell)
    (same : LargeExponentSamePhaseContext first second) (geometry : TailPhaseGeometry) :
    finitePhaseAnalyticChecked first geometry = finitePhaseAnalyticChecked second geometry := by
  rcases same with ⟨layer,endpoint_depth,height,vertical_depth,endpoint⟩
  simp only [finitePhaseAnalyticChecked,finitePhaseCenter,finitePhaseLength,
    layer,endpoint_depth,height,vertical_depth,endpoint]

end LambdaCantor.RationalPowers
