import LambdaCantor.Integer.FixedLogArithmetic
import LambdaCantor.Certificates.IntegerLogSourceDefinition

namespace LambdaCantor.Integer

def logCertificateScale : ℕ := 2^256
def logCertificateTerms : ℕ := 80

/-- The analytic part of a source certificate, checked entirely with natural
interval arithmetic. The source geometry and slope band are checked separately. -/
def LogSourceData.LogChecked (n exponent : ℕ) (source : LogSourceData) : Prop :=
  0 < source.P ∧ 0 < source.Q ∧
  source.P+1 ≤ 3^source.p ∧ source.Q+1 ≤ 3^source.q ∧
  3^exponent ≤ n ∧
  (logParameter logCertificateScale (3^source.p) source.P).upper < logCertificateScale ∧
  (logParameter logCertificateScale (3^source.p) (source.P+1)).upper < logCertificateScale ∧
  (logParameter logCertificateScale (3^source.q) source.Q).upper < logCertificateScale ∧
  (logParameter logCertificateScale (3^source.q) (source.Q+1)).upper < logCertificateScale ∧
  (logParameter logCertificateScale n (3^exponent)).upper < logCertificateScale ∧
  let logUmin := logUnitInterval logCertificateScale (3^source.p) source.P logCertificateTerms
  let logUmax := logUnitInterval logCertificateScale (3^source.p) (source.P+1) logCertificateTerms
  let logVmin := logUnitInterval logCertificateScale (3^source.q) source.Q logCertificateTerms
  let logVmax := logUnitInterval logCertificateScale (3^source.q) (source.Q+1) logCertificateTerms
  let logN := logIntegerInterval logCertificateScale n exponent logCertificateTerms
  let logThree := logUnitInterval logCertificateScale 3 1 logCertificateTerms
  (n : ℤ)*logUmin.lower+logN.lower >
    (logVmax.upper : ℤ)+(source.d : ℤ)*logThree.upper ∧
  (n : ℤ)*logUmax.upper+logN.upper <
    (logVmin.lower : ℤ)+(source.d : ℤ)*logThree.lower

instance (n exponent : ℕ) (source : LogSourceData) :
    Decidable (source.LogChecked n exponent) := by
  unfold LogSourceData.LogChecked
  infer_instance

theorem LogSourceData.LogChecked.real_log_corners {n exponent : ℕ} {source : LogSourceData}
    (checked : source.LogChecked n exponent) :
    (n : ℝ)*Real.log ((source.P : ℝ)/3^source.p) -
        Real.log ((source.Q+1)/3^source.q) - Real.log n +
        (source.d : ℝ)*Real.log 3 < 0 ∧
    0 < (n : ℝ)*Real.log ((source.P+1)/3^source.p) -
        Real.log ((source.Q : ℝ)/3^source.q) - Real.log n +
        (source.d : ℝ)*Real.log 3 := by
  obtain ⟨positiveP,positiveQ,boundP,boundQ,ordered,
    strictP,strictPnext,strictQ,strictQnext,strictN,lower,upper⟩ := checked
  have scalePositive : 0 < logCertificateScale := by decide
  have threeStrict : (logParameter logCertificateScale 3 1).upper < logCertificateScale := by
    decide
  have logThree := logUnitInterval_sound logCertificateScale 3 1 logCertificateTerms
    scalePositive (by decide) (by decide) threeStrict
  simp only [Nat.cast_ofNat,Nat.cast_one,div_one] at logThree
  have logN := logIntegerInterval_sound logCertificateScale n exponent logCertificateTerms
    scalePositive ordered strictN threeStrict
  have logP := logUnitInterval_sound logCertificateScale (3^source.p) source.P
    logCertificateTerms scalePositive positiveP (by omega) strictP
  have logPnext := logUnitInterval_sound logCertificateScale (3^source.p) (source.P+1)
    logCertificateTerms scalePositive (by omega) boundP strictPnext
  have logQ := logUnitInterval_sound logCertificateScale (3^source.q) source.Q
    logCertificateTerms scalePositive positiveQ (by omega) strictQ
  have logQnext := logUnitInterval_sound logCertificateScale (3^source.q) (source.Q+1)
    logCertificateTerms scalePositive (by omega) boundQ strictQnext
  have negative := strict_log_corner_of_intervals scalePositive logP logQnext logN logThree lower
  have positive := strict_log_corner_positive_of_intervals scalePositive
    logPnext logQ logN logThree upper
  have realP : (source.P : ℝ) ≠ 0 := by positivity
  have realQ : (source.Q : ℝ) ≠ 0 := by positivity
  have realPnext : ((source.P : ℝ)+1) ≠ 0 := by positivity
  have realQnext : ((source.Q : ℝ)+1) ≠ 0 := by positivity
  have powerP : (3 : ℝ)^source.p ≠ 0 := by positivity
  have powerQ : (3 : ℝ)^source.q ≠ 0 := by positivity
  push_cast at negative positive
  rw [Real.log_div powerP realP,Real.log_div powerQ realQnext] at negative
  rw [Real.log_div powerP realPnext,Real.log_div powerQ realQ] at positive
  rw [Real.log_div realP powerP,Real.log_div realQnext powerQ,
    Real.log_div realPnext powerP,Real.log_div realQ powerQ]
  constructor <;> nlinarith

end LambdaCantor.Integer
