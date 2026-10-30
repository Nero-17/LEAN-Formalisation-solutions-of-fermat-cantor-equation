import LambdaCantor.RationalPowers.ExceptionalSource
import LambdaCantor.RationalPowers.LowIndexEncoding
import LambdaCantor.Integer.ExceptionalCertificate
import LambdaCantor.RealPowers.ExponentCases

namespace LambdaCantor.RationalPowers
open LambdaCantor.Integer.Exceptional

/-- One of the seven exceptions carries its actual real-power source and
finite integer return DAG. Every geometric, enclosure and return acceptance
condition remains executable and is exposed in Checked. -/
structure LowExceptionalCertificate where
  numerator : ℕ
  denominator : ℕ
  source : Exceptional.PowerSource
  latticeDenominator : ℤ
  offsets : Fin 4 → ℤ
  outerIntervals : List (ℤ × ℤ)
  innerIntervals : List (ℤ × ℤ)
  nodes : Array Node
  roots : List ℕ
  maximumDepth : ℕ

def LowExceptionalCertificate.Checked (certificate : LowExceptionalCertificate) : Prop :=
  certificate.source.Valid ∧ 0 < certificate.latticeDenominator ∧
  certificate.source.exponent = (certificate.numerator : ℚ)/certificate.denominator ∧
  certificate.source.returnDepth = certificate.maximumDepth ∧
  (∀ digit : Fin 4, (certificate.offsets digit : ℚ)/certificate.latticeDenominator =
    match digit.val with | 0 => 0 | 1 => 1 | 2 => certificate.source.slope | _ => certificate.source.slope+1) ∧
  certificate.outerIntervals.map (fun interval =>
    ((interval.1 : ℚ)/certificate.latticeDenominator,(interval.2 : ℚ)/certificate.latticeDenominator)) =
    [(1/3,(certificate.source.slope+1)/6),(certificate.source.slope/3,(certificate.source.slope+3)/6),
      ((certificate.source.slope+1)/3,(3*certificate.source.slope+1)/6)] ∧
  certificate.innerIntervals.map (fun interval =>
    ((interval.1 : ℚ)/certificate.latticeDenominator,(interval.2 : ℚ)/certificate.latticeDenominator)) =
    [(1/3+certificate.source.margin,(certificate.source.slope+1)/6-certificate.source.margin),
      (certificate.source.slope/3+certificate.source.margin,(certificate.source.slope+3)/6-certificate.source.margin),
      ((certificate.source.slope+1)/3+certificate.source.margin,(3*certificate.source.slope+1)/6-certificate.source.margin)] ∧
  checkCertificate certificate.latticeDenominator certificate.offsets certificate.innerIntervals certificate.nodes = true ∧
  checkRoots certificate.outerIntervals certificate.nodes certificate.roots certificate.maximumDepth = true ∧
  (certificate.numerator,certificate.denominator) ∈ RealPowers.rationalExceptionalPairs

instance lowExceptionalCertificateCheckedDecidable (certificate : LowExceptionalCertificate) : Decidable certificate.Checked := by
  unfold LowExceptionalCertificate.Checked
  infer_instance

end LambdaCantor.RationalPowers
