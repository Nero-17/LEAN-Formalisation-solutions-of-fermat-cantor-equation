import LambdaCantor.Certificates.IntegerSmallSources
import Mathlib.Data.Rat.Cast.Order

namespace LambdaCantor.Integer.Exceptional

/-- Exact source and rational slope used by the nine direct-return certificates. -/
structure Source where
  exponent : ℕ
  horizontal : ℕ
  vertical : ℕ
  horizontalDepth : ℕ
  verticalDepth : ℕ
  slope : ℚ
  returnDepth : ℕ
  deriving Repr

def Source.scale (source : Source) : ℕ :=
  3 ^ (source.exponent * (source.verticalDepth - source.horizontalDepth))

def Source.actualSlope (source : Source) : ℚ :=
  (source.vertical : ℚ) ^ (source.exponent - 1) /
    (source.scale * (source.horizontal : ℚ) ^ (source.exponent - 1))

def Source.intercept (source : Source) : ℚ :=
  ((3 : ℚ) ^ (source.exponent * source.verticalDepth) -
      source.scale * (source.horizontal : ℚ) ^ source.exponent -
      (source.vertical : ℚ) ^ source.exponent) /
    (2 * source.exponent * source.scale * (source.horizontal : ℚ) ^ (source.exponent - 1))

def Source.error (source : Source) : ℚ :=
  (((source.vertical : ℚ) + 1) ^ (source.exponent - 1) -
      (source.vertical : ℚ) ^ (source.exponent - 1)) /
    (2 * source.scale * (source.horizontal : ℚ) ^ (source.exponent - 1)) +
  (((source.horizontal : ℚ) + 1) ^ (source.exponent - 1) -
      (source.horizontal : ℚ) ^ (source.exponent - 1)) /
    (2 * (source.horizontal : ℚ) ^ (source.exponent - 1)) +
  (source.actualSlope - source.slope) / 2

def Source.Valid (source : Source) : Prop :=
  3 ≤ source.exponent ∧ 0 < source.horizontal ∧ 0 < source.vertical ∧
  source.horizontalDepth ≤ source.verticalDepth ∧
  ternaryPrefix source.horizontal source.horizontalDepth = true ∧
  ternaryPrefix source.vertical source.verticalDepth = true ∧
  source.horizontal + 1 ≤ 3 ^ source.horizontalDepth ∧
  source.vertical + 1 ≤ 3 ^ source.verticalDepth ∧
  source.scale * source.horizontal ^ source.exponent + source.vertical ^ source.exponent <
    3 ^ (source.exponent * source.verticalDepth) ∧
  3 ^ (source.exponent * source.verticalDepth) <
    source.scale * (source.horizontal + 1) ^ source.exponent +
      (source.vertical + 1) ^ source.exponent ∧
  1 < source.slope ∧ source.slope < 3 ∧ source.slope ≤ source.actualSlope ∧
  ((1 / 3 < source.intercept ∧ source.intercept < (source.slope + 1) / 6) ∨
    (source.slope / 3 < source.intercept ∧ source.intercept < (source.slope + 3) / 6) ∨
    ((source.slope + 1) / 3 < source.intercept ∧
      source.intercept < (3 * source.slope + 1) / 6)) ∧
  (3 : ℚ) ^ source.returnDepth * source.error < 1 / 100000

instance (source : Source) : Decidable source.Valid := by
  unfold Source.Valid
  infer_instance

/-- Quantitative derivative gaps needed by the retained-square crossing theorem. -/
def Source.MarginValid (source : Source) : Prop :=
  0 ≤ source.error ∧ source.error ≤ 1 / 2 ∧
  4 * source.error ≤ source.slope - 1 ∧
  8 * source.error ≤ 3 - source.slope

instance (source : Source) : Decidable source.MarginValid := by
  unfold Source.MarginValid
  infer_instance

end LambdaCantor.Integer.Exceptional
