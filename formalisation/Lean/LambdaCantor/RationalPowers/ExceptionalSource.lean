import LambdaCantor.Analysis.RationalPowerEnclosure
import LambdaCantor.Certificates.IntegerSmallSources

namespace LambdaCantor.RationalPowers.Exceptional

structure PowerBounds where
  lower : ℚ
  upper : ℚ
  deriving Repr

def PowerBounds.check (bounds : PowerBounds) (base : ℚ) (numerator : ℤ) (denominator : ℕ) : Bool :=
  Analysis.rationalPowerEnclosureCheck base numerator denominator bounds.lower bounds.upper

theorem PowerBounds.sound {bounds : PowerBounds} {base : ℚ} {numerator : ℤ} {denominator : ℕ}
    (checked : bounds.check base numerator denominator = true) :
    (bounds.lower : ℝ) ≤ (base : ℝ)^((numerator : ℝ)/(denominator : ℝ)) ∧
      (base : ℝ)^((numerator : ℝ)/(denominator : ℝ)) ≤ (bounds.upper : ℝ) :=
  Analysis.rationalPowerEnclosureCheck_sound checked

/-- All numerical inputs are rational. The normalization is a rational
reference value, rather than an unverified algebraic derivative value. -/
structure PowerSource where
  numerator : ℤ
  denominator : ℕ
  horizontal : ℕ
  vertical : ℕ
  horizontalDepth : ℕ
  verticalDepth : ℕ
  slope : ℚ
  normalization : ℚ
  returnDepth : ℕ
  margin : ℚ
  horizontalValue : PowerBounds
  verticalValue : PowerBounds
  horizontalDerivative : PowerBounds
  verticalDerivative : PowerBounds
  horizontalSecond : PowerBounds
  horizontalSecondUpper : PowerBounds
  verticalSecond : PowerBounds
  verticalSecondUpper : PowerBounds
  horizontalCoefficientError : ℚ
  verticalCoefficientError : ℚ
  deriving Repr

def PowerSource.exponent (source : PowerSource) : ℚ := source.numerator / source.denominator
def PowerSource.horizontalScale (source : PowerSource) : ℚ := 1 / (3 : ℚ)^source.horizontalDepth
def PowerSource.verticalScale (source : PowerSource) : ℚ := 1 / (3 : ℚ)^source.verticalDepth
def PowerSource.horizontalBase (source : PowerSource) : ℚ := source.horizontal * source.horizontalScale
def PowerSource.verticalBase (source : PowerSource) : ℚ := source.vertical * source.verticalScale

def PowerSource.error (source : PowerSource) : ℚ :=
  (source.horizontalScale^2 *
      (source.exponent * |source.exponent-1| *
        max source.horizontalSecond.upper source.horizontalSecondUpper.upper) +
    source.verticalScale^2 *
      (source.exponent * |source.exponent-1| *
        max source.verticalSecond.upper source.verticalSecondUpper.upper)) / source.normalization +
    source.horizontalCoefficientError + source.verticalCoefficientError

def PowerSource.levelLower (source : PowerSource) : ℚ :=
  (1-source.horizontalValue.upper-source.verticalValue.upper)/source.normalization
def PowerSource.levelUpper (source : PowerSource) : ℚ :=
  (1-source.horizontalValue.lower-source.verticalValue.lower)/source.normalization

def PowerSource.GeometryValid (source : PowerSource) : Prop :=
  0 < source.denominator ∧ 1 < source.exponent ∧
  0 < source.horizontal ∧ 0 < source.vertical ∧
  Integer.ternaryPrefix source.horizontal source.horizontalDepth = true ∧
  Integer.ternaryPrefix source.vertical source.verticalDepth = true ∧
  source.horizontal + 1 ≤ 3^source.horizontalDepth ∧
  source.vertical + 1 ≤ 3^source.verticalDepth ∧
  1 < source.slope ∧ source.slope < 3 ∧ 0 < source.normalization ∧ 0 < source.margin

def PowerSource.EnclosuresValid (source : PowerSource) : Prop :=
  source.horizontalValue.check source.horizontalBase source.numerator source.denominator = true ∧
  source.verticalValue.check source.verticalBase source.numerator source.denominator = true ∧
  source.horizontalDerivative.check source.horizontalBase
    (source.numerator-source.denominator) source.denominator = true ∧
  source.verticalDerivative.check source.verticalBase
    (source.numerator-source.denominator) source.denominator = true ∧
  source.horizontalSecond.check source.horizontalBase
    (source.numerator-2*source.denominator) source.denominator = true ∧
  source.horizontalSecondUpper.check (source.horizontalBase+source.horizontalScale)
    (source.numerator-2*source.denominator) source.denominator = true ∧
  source.verticalSecond.check source.verticalBase
    (source.numerator-2*source.denominator) source.denominator = true ∧
  source.verticalSecondUpper.check (source.verticalBase+source.verticalScale)
    (source.numerator-2*source.denominator) source.denominator = true

def PowerSource.ErrorValid (source : PowerSource) : Prop :=
  0 ≤ source.horizontalCoefficientError ∧ 0 ≤ source.verticalCoefficientError ∧
  |source.exponent*source.horizontalDerivative.lower*source.horizontalScale/source.normalization-source.slope/2| ≤
    source.horizontalCoefficientError ∧
  |source.exponent*source.horizontalDerivative.upper*source.horizontalScale/source.normalization-source.slope/2| ≤
    source.horizontalCoefficientError ∧
  |source.exponent*source.verticalDerivative.lower*source.verticalScale/source.normalization-1/2| ≤
    source.verticalCoefficientError ∧
  |source.exponent*source.verticalDerivative.upper*source.verticalScale/source.normalization-1/2| ≤
    source.verticalCoefficientError ∧
  0 ≤ source.error ∧ (3 : ℚ)^source.returnDepth*source.error < source.margin

def PowerSource.LevelValid (source : PowerSource) : Prop :=
  (1/3 < source.levelLower ∧ source.levelUpper < (source.slope+1)/6) ∨
  (source.slope/3 < source.levelLower ∧ source.levelUpper < (source.slope+3)/6) ∨
  ((source.slope+1)/3 < source.levelLower ∧ source.levelUpper < (3*source.slope+1)/6)

def PowerSource.Valid (source : PowerSource) : Prop :=
  source.GeometryValid ∧ source.EnclosuresValid ∧ source.ErrorValid ∧ source.LevelValid

instance (source : PowerSource) : Decidable source.Valid := by
  unfold PowerSource.Valid PowerSource.GeometryValid PowerSource.EnclosuresValid
    PowerSource.ErrorValid PowerSource.LevelValid
  infer_instance

end LambdaCantor.RationalPowers.Exceptional
