import LambdaCantor.Last.TwoBandCriterion
import LambdaCantor.Last.EndpointDepthSequences
import LambdaCantor.Last.EndpointTransferEmbedding

noncomputable section
namespace LambdaCantor.Last

/-- A fixed positive cylinder rectangle and the integer endpoint coefficient.
All hulls are actual scalar Cantor cylinders. -/
structure EndpointRectangle (exponent ratio : ℝ) where
  firstWord : List Bool
  secondWord : List Bool
  firstOffset : ℕ
  secondOffset : ℤ
  first_positive : 0 < scalarWordMap ratio firstWord 0
  second_positive : 0 < scalarWordMap ratio secondWord 0
  lower_corner : (scalarWordMap ratio firstWord 0) ^ exponent <
    exponent * ratio ^ ((secondOffset : ℝ) - firstOffset * exponent) * scalarWordMap ratio secondWord 1
  upper_corner : exponent * ratio ^ ((secondOffset : ℝ) - firstOffset * exponent) *
    scalarWordMap ratio secondWord 0 < (scalarWordMap ratio firstWord 1) ^ exponent

def EndpointRectangle.powerLower {exponent ratio : ℝ} (source : EndpointRectangle exponent ratio) : ℝ :=
  ratio ^ ((source.secondOffset : ℝ) - source.firstOffset * exponent +
    source.secondWord.length - source.firstWord.length) *
    (scalarWordMap ratio source.firstWord 1) ^ (1 - exponent)

def EndpointRectangle.powerUpper {exponent ratio : ℝ} (source : EndpointRectangle exponent ratio) : ℝ :=
  ratio ^ ((source.secondOffset : ℝ) - source.firstOffset * exponent +
    source.secondWord.length - source.firstWord.length) *
    (scalarWordMap ratio source.firstWord 0) ^ (1 - exponent)

def EndpointRectangle.logLower {exponent ratio : ℝ} (source : EndpointRectangle exponent ratio) : ℝ :=
  exponent * ratio ^ ((source.firstWord.length : ℝ) - source.secondWord.length) *
    scalarWordMap ratio source.secondWord 0 / scalarWordMap ratio source.firstWord 1

def EndpointRectangle.logUpper {exponent ratio : ℝ} (source : EndpointRectangle exponent ratio) : ℝ :=
  exponent * ratio ^ ((source.firstWord.length : ℝ) - source.secondWord.length) *
    scalarWordMap ratio source.secondWord 1 / scalarWordMap ratio source.firstWord 0

/-- Both derivative orientations are allowed, for either zero-equivalent form. -/
def EndpointRectangle.Accepted {exponent ratio : ℝ} (source : EndpointRectangle exponent ratio) : Prop :=
  TwoBandInterval ratio source.powerLower source.powerUpper ∨
  TwoBandInterval ratio (1 / source.powerUpper) (1 / source.powerLower) ∨
  TwoBandInterval ratio source.logLower source.logUpper ∨
  TwoBandInterval ratio (1 / source.logUpper) (1 / source.logLower)

end LambdaCantor.Last
