import LambdaCantor.RationalPowers.FixedLogCorners
import LambdaCantor.Integer.FixedLogArithmetic
import LambdaCantor.Integer.TernaryPrefixSoundness

namespace LambdaCantor.RationalPowers
open Integer

def rationalLogScale : ℕ := 2^256
def rationalLogTerms : ℕ := 80

structure RationalLogSource where
  numerator : ℕ
  denominator : ℕ
  horizontal : ℕ
  vertical : ℕ
  horizontalDepth : ℕ
  verticalDepth : ℕ
  phaseNumerator : ℤ
  numeratorReduction : ℕ
  denominatorReduction : ℕ
deriving DecidableEq

def differenceNatIntervals (first second : NatInterval) : IntInterval :=
  ⟨(first.lower : ℤ)-second.upper,(first.upper : ℤ)-second.lower⟩

theorem differenceNatIntervals_sound {scale : ℕ} (first second : NatInterval) (x y : ℝ)
    (first_enclosed : first.Encloses scale x) (second_enclosed : second.Encloses scale y) :
    (differenceNatIntervals first second).Encloses scale (x-y) := by
  simp only [differenceNatIntervals, IntInterval.Encloses, Int.cast_sub, Int.cast_natCast]
  constructor <;> nlinarith [first_enclosed.1, first_enclosed.2, second_enclosed.1, second_enclosed.2]

/-- Explicit cache values may be shared across all sources using identical
positive endpoints or the same reduced exponent. Their soundness is proved
from the fixed-point logarithm algorithms, not asserted in the source data. -/
structure RationalLogCache where
  horizontalLeft : IntInterval
  horizontalRight : IntInterval
  verticalLeft : IntInterval
  verticalRight : IntInterval
  exponent : IntInterval
  three : IntInterval
deriving DecidableEq

def RationalLogSource.cache (source : RationalLogSource) : RationalLogCache :=
  { horizontalLeft := signedLogInterval rationalLogScale source.horizontal (3^source.horizontalDepth) rationalLogTerms
    horizontalRight := signedLogInterval rationalLogScale (source.horizontal+1) (3^source.horizontalDepth) rationalLogTerms
    verticalLeft := signedLogInterval rationalLogScale source.vertical (3^source.verticalDepth) rationalLogTerms
    verticalRight := signedLogInterval rationalLogScale (source.vertical+1) (3^source.verticalDepth) rationalLogTerms
    exponent := differenceNatIntervals
      (logIntegerInterval rationalLogScale source.numerator source.numeratorReduction rationalLogTerms)
      (logIntegerInterval rationalLogScale source.denominator source.denominatorReduction rationalLogTerms)
    three := signedLogInterval rationalLogScale 3 1 rationalLogTerms }

def RationalLogSource.AnalyticChecked (source : RationalLogSource) : Prop :=
  0 < source.numerator ∧ 0 < source.denominator ∧
  0 < source.horizontal ∧ 0 < source.vertical ∧
  3^source.numeratorReduction ≤ source.numerator ∧
  3^source.denominatorReduction ≤ source.denominator ∧
  (logParameter rationalLogScale source.numerator (3^source.numeratorReduction)).upper < rationalLogScale ∧
  (logParameter rationalLogScale source.denominator (3^source.denominatorReduction)).upper < rationalLogScale ∧
  signedLogStrict rationalLogScale source.horizontal (3^source.horizontalDepth) ∧
  signedLogStrict rationalLogScale (source.horizontal+1) (3^source.horizontalDepth) ∧
  signedLogStrict rationalLogScale source.vertical (3^source.verticalDepth) ∧
  signedLogStrict rationalLogScale (source.vertical+1) (3^source.verticalDepth)

instance (source : RationalLogSource) : Decidable source.AnalyticChecked := by
  unfold RationalLogSource.AnalyticChecked
  infer_instance

def RationalLogCache.Encloses (cache : RationalLogCache) (source : RationalLogSource) : Prop :=
  cache.horizontalLeft.Encloses rationalLogScale (Real.log ((source.horizontal : ℝ)/3^source.horizontalDepth)) ∧
  cache.horizontalRight.Encloses rationalLogScale (Real.log ((source.horizontal+1 : ℝ)/3^source.horizontalDepth)) ∧
  cache.verticalLeft.Encloses rationalLogScale (Real.log ((source.vertical : ℝ)/3^source.verticalDepth)) ∧
  cache.verticalRight.Encloses rationalLogScale (Real.log ((source.vertical+1 : ℝ)/3^source.verticalDepth)) ∧
  cache.exponent.Encloses rationalLogScale (Real.log ((source.numerator : ℝ)/source.denominator)) ∧
  cache.three.Encloses rationalLogScale (Real.log 3)

theorem RationalLogSource.AnalyticChecked.cache_sound {source : RationalLogSource}
    (checked : source.AnalyticChecked) : source.cache.Encloses source := by
  obtain ⟨numerator_positive, denominator_positive, horizontal_positive, vertical_positive,
    numerator_ordered, denominator_ordered, numerator_strict, denominator_strict,
    horizontal_strict, horizontal_next_strict, vertical_strict, vertical_next_strict⟩ := checked
  have scale_positive : 0 < rationalLogScale := by decide
  have three_strict : (logParameter rationalLogScale 3 1).upper < rationalLogScale := by decide
  have signed_three_strict : signedLogStrict rationalLogScale 3 1 := by decide
  have numerator_enclosed := logIntegerInterval_sound rationalLogScale source.numerator
    source.numeratorReduction rationalLogTerms scale_positive numerator_ordered numerator_strict three_strict
  have denominator_enclosed := logIntegerInterval_sound rationalLogScale source.denominator
    source.denominatorReduction rationalLogTerms scale_positive denominator_ordered denominator_strict three_strict
  have exponent_enclosed := differenceNatIntervals_sound _ _ _ _ numerator_enclosed denominator_enclosed
  rw [← Real.log_div (by positivity : (source.numerator : ℝ) ≠ 0)
    (by positivity : (source.denominator : ℝ) ≠ 0)] at exponent_enclosed
  dsimp only [RationalLogCache.Encloses, RationalLogSource.cache]
  refine ⟨?_, ?_, ?_, ?_, exponent_enclosed, ?_⟩
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      signedLogInterval_sound rationalLogScale source.horizontal (3^source.horizontalDepth)
        rationalLogTerms scale_positive horizontal_positive (by positivity) horizontal_strict
  · simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using
      signedLogInterval_sound rationalLogScale (source.horizontal+1) (3^source.horizontalDepth)
        rationalLogTerms scale_positive (by omega) (by positivity) horizontal_next_strict
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      signedLogInterval_sound rationalLogScale source.vertical (3^source.verticalDepth)
        rationalLogTerms scale_positive vertical_positive (by positivity) vertical_strict
  · simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using
      signedLogInterval_sound rationalLogScale (source.vertical+1) (3^source.verticalDepth)
        rationalLogTerms scale_positive (by omega) (by positivity) vertical_next_strict
  · simpa only [Nat.cast_ofNat, Nat.cast_one, div_one] using
      signedLogInterval_sound rationalLogScale 3 1 rationalLogTerms scale_positive
        (by decide) (by decide) signed_three_strict

/-- This is the cheap per-row integer predicate after the shared logarithm
cache has been computed. No large powers P^a occur in it. -/
def RationalLogCache.CornersChecked (cache : RationalLogCache) (source : RationalLogSource) : Prop :=
  let phase := scaleSignedInterval source.phaseNumerator cache.three
  phase.upper+(source.numerator : ℤ)*cache.horizontalLeft.upper-
    (source.denominator : ℤ)*cache.exponent.lower-(source.denominator : ℤ)*cache.verticalRight.lower < 0 ∧
  0 < phase.lower+(source.numerator : ℤ)*cache.horizontalRight.lower-
    (source.denominator : ℤ)*cache.exponent.upper-(source.denominator : ℤ)*cache.verticalLeft.upper

instance (cache : RationalLogCache) (source : RationalLogSource) :
    Decidable (cache.CornersChecked source) := by
  unfold RationalLogCache.CornersChecked
  infer_instance

theorem RationalLogCache.CornersChecked.real_log_corners {source : RationalLogSource}
    {cache : RationalLogCache} (enclosed : cache.Encloses source)
    (denominator_positive : 0 < source.denominator) (checked : cache.CornersChecked source) :
    ((source.phaseNumerator : ℝ)/source.denominator)*Real.log 3+
      ((source.numerator : ℝ)/source.denominator)*
        Real.log ((source.horizontal : ℝ)/3^source.horizontalDepth)-
      Real.log ((source.numerator : ℝ)/source.denominator)-
        Real.log ((source.vertical+1 : ℝ)/3^source.verticalDepth) < 0 ∧
    0 < ((source.phaseNumerator : ℝ)/source.denominator)*Real.log 3+
      ((source.numerator : ℝ)/source.denominator)*
        Real.log ((source.horizontal+1 : ℝ)/3^source.horizontalDepth)-
      Real.log ((source.numerator : ℝ)/source.denominator)-
        Real.log ((source.vertical : ℝ)/3^source.verticalDepth) := by
  have phase_enclosed := scaleSignedInterval_sound source.phaseNumerator cache.three (Real.log 3)
    enclosed.2.2.2.2.2
  constructor
  · exact negative_rational_log_corner source.phaseNumerator (by decide) denominator_positive
      _ _ _ _ _ _ _ phase_enclosed enclosed.1 enclosed.2.2.2.1 enclosed.2.2.2.2.1 checked.1
  · exact positive_rational_log_corner source.phaseNumerator (by decide) denominator_positive
      _ _ _ _ _ _ _ phase_enclosed enclosed.2.1 enclosed.2.2.1 enclosed.2.2.2.2.1 checked.2

def RationalLogSource.Checked (source : RationalLogSource) : Prop :=
  source.AnalyticChecked ∧ source.cache.CornersChecked source ∧
  source.numerator.Coprime source.denominator ∧
  Integer.ternaryPrefix source.horizontal source.horizontalDepth = true ∧
  Integer.ternaryPrefix source.vertical source.verticalDepth = true

instance (source : RationalLogSource) : Decidable source.Checked := by
  unfold RationalLogSource.Checked
  infer_instance

theorem RationalLogSource.Checked.real_log_corners {source : RationalLogSource}
    (checked : source.Checked) :
    ((source.phaseNumerator : ℝ)/source.denominator)*Real.log 3+
      ((source.numerator : ℝ)/source.denominator)*
        Real.log ((source.horizontal : ℝ)/3^source.horizontalDepth)-
      Real.log ((source.numerator : ℝ)/source.denominator)-
        Real.log ((source.vertical+1 : ℝ)/3^source.verticalDepth) < 0 ∧
    0 < ((source.phaseNumerator : ℝ)/source.denominator)*Real.log 3+
      ((source.numerator : ℝ)/source.denominator)*
        Real.log ((source.horizontal+1 : ℝ)/3^source.horizontalDepth)-
      Real.log ((source.numerator : ℝ)/source.denominator)-
        Real.log ((source.vertical : ℝ)/3^source.verticalDepth) :=
  RationalLogCache.CornersChecked.real_log_corners checked.1.cache_sound checked.1.2.1 checked.2.1

end LambdaCantor.RationalPowers

