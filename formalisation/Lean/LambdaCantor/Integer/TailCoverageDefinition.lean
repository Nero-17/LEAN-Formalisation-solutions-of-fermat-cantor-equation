import LambdaCantor.Integer.TailPhaseChecker
import LambdaCantor.Certificates.IntegerTailEndpoints

namespace LambdaCantor.Integer

/-- The original finite tail-coverage obligation, separated from its analytic
application so native certificate blocks need only the executable checker. -/
def TailCoverageCertified : Prop :=
  ∀ row ∈ tailParameterRows, ∀ cell : ℕ, row.2.1 ≤ cell → cell ≤ row.2.2 →
    ∃ sources : Array TailPhaseGeometry, ∃ arcs : List TailPhaseArc,
      tailPhaseCellCheck sources cell arcs = true

end LambdaCantor.Integer
