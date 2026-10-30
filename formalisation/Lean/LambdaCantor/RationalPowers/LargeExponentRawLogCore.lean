import LambdaCantor.RationalPowers.LargeExponentRawPhaseCore

namespace LambdaCantor.RationalPowers.RawLog

/-- Integer-only extraction of the fixed-point logarithm computation. -/
structure NatInterval where
  lower : Nat
  upper : Nat
  deriving DecidableEq

def NatInterval.add (first second : NatInterval) : NatInterval :=
  ⟨first.lower+second.lower,first.upper+second.upper⟩

def NatInterval.divide (bounds : NatInterval) (denominator : Nat) : NatInterval :=
  ⟨bounds.lower/denominator,bounds.upper/denominator+1⟩

def NatInterval.mulThree (scale : Nat) (first second third : NatInterval) : NatInterval :=
  ⟨first.lower*second.lower*third.lower/(scale*scale),
    first.upper*second.upper*third.upper/(scale*scale)+1⟩

def atanhLoop (scale : Nat) (parameter : NatInterval) : Nat → NatInterval × NatInterval
  | 0 => (parameter,⟨0,0⟩)
  | terms+1 =>
    let previous := atanhLoop scale parameter terms
    (NatInterval.mulThree scale previous.1 parameter parameter,
      previous.2.add ((previous.1.add previous.1).divide (2*terms+1)))

def atanhInterval (scale : Nat) (parameter : NatInterval) (terms : Nat) : NatInterval :=
  let result := atanhLoop scale parameter terms
  ⟨result.2.lower,result.2.upper+
    (2*result.1.upper*scale)/(scale-parameter.upper)+1⟩

def logParameter (scale numerator denominator : Nat) : NatInterval :=
  ⟨scale*(numerator-denominator)/(numerator+denominator),
    scale*(numerator-denominator)/(numerator+denominator)+1⟩

def logUnitInterval (scale numerator denominator terms : Nat) : NatInterval :=
  atanhInterval scale (logParameter scale numerator denominator) terms

def signedLogInterval (scale numerator denominator terms : Nat) : RawPhase.Interval :=
  if denominator ≤ numerator then
    let result := logUnitInterval scale numerator denominator terms
    ⟨result.lower,result.upper⟩
  else
    let result := logUnitInterval scale denominator numerator terms
    ⟨-(result.upper : Int),-(result.lower : Int)⟩

def signedLogStrict (scale numerator denominator : Nat) : Prop :=
  if denominator ≤ numerator then (logParameter scale numerator denominator).upper < scale
  else (logParameter scale denominator numerator).upper < scale

instance (scale numerator denominator : Nat) :
    Decidable (signedLogStrict scale numerator denominator) := by
  unfold signedLogStrict
  infer_instance

def scaleBy (bounds : RawPhase.Interval) (coefficient : Nat) : RawPhase.Interval :=
  ⟨coefficient*bounds.lower,coefficient*bounds.upper⟩

def divideBetween (numerator denominator : RawPhase.Interval) : RawPhase.Interval :=
  ⟨min (numerator.lower/denominator.lower) (numerator.lower/denominator.upper),
    max (numerator.upper/denominator.lower) (numerator.upper/denominator.upper)+1⟩

def LogRatioChecked (scale numerator denominator : Nat) : Prop :=
  0 < scale ∧ 0 < numerator ∧ 0 < denominator ∧
    signedLogStrict scale numerator denominator ∧ signedLogStrict scale 3 1 ∧
    0 < (signedLogInterval scale 3 1 80).lower ∧
    0 < (signedLogInterval scale 3 1 80).upper

instance (scale numerator denominator : Nat) :
    Decidable (LogRatioChecked scale numerator denominator) := by
  unfold LogRatioChecked
  infer_instance

def logRatioLatticeInterval (scale multiple numerator denominator terms : Nat) : RawPhase.Interval :=
  divideBetween (scaleBy (signedLogInterval scale numerator denominator terms) multiple)
    (signedLogInterval scale 3 1 80)

def finitePhaseOffsetInterval (cell : RawPhase.Cell) (geometry : RawPhase.Geometry)
    (offset : Nat) : RawPhase.Interval :=
  logRatioLatticeInterval (2^256) (2^80*3^cell.m)
    (2*RawPhase.center cell*RawPhase.length cell geometry+3^cell.height*RawPhase.length cell geometry)
    (2*RawPhase.center cell*RawPhase.length cell geometry+2*offset) 12

def finitePhaseCache (cell : RawPhase.Cell) (geometry : RawPhase.Geometry) : RawPhase.Cache :=
  { qLog := logRatioLatticeInterval (2^256) (2^80) geometry.q (3^(cell.verticalDepth+1)) 80
    nextQLog := logRatioLatticeInterval (2^256) (2^80) (geometry.q+1) (3^(cell.verticalDepth+1)) 80
    atOffset := finitePhaseOffsetInterval cell geometry geometry.a
    atNextOffset := finitePhaseOffsetInterval cell geometry (geometry.a+1) }

def finitePhaseAnalyticChecked (cell : RawPhase.Cell) (geometry : RawPhase.Geometry) : Prop :=
  LogRatioChecked (2^256) geometry.q (3^(cell.verticalDepth+1)) ∧
  LogRatioChecked (2^256) (geometry.q+1) (3^(cell.verticalDepth+1)) ∧
  LogRatioChecked (2^256)
    (2*RawPhase.center cell*RawPhase.length cell geometry+3^cell.height*RawPhase.length cell geometry)
    (2*RawPhase.center cell*RawPhase.length cell geometry+2*geometry.a) ∧
  LogRatioChecked (2^256)
    (2*RawPhase.center cell*RawPhase.length cell geometry+3^cell.height*RawPhase.length cell geometry)
    (2*RawPhase.center cell*RawPhase.length cell geometry+2*(geometry.a+1))

instance (cell : RawPhase.Cell) (geometry : RawPhase.Geometry) :
    Decidable (finitePhaseAnalyticChecked cell geometry) := by
  unfold finitePhaseAnalyticChecked
  infer_instance

/-- Named here to leave the raw phase namespace's instance names available. -/
instance rawPhaseIntervalDecidableEq : DecidableEq RawPhase.Interval := by
  intro first second
  exact decidable_of_iff (first.lower = second.lower ∧ first.upper = second.upper) (by
    constructor
    · intro equal
      cases first
      cases second
      cases equal.1
      cases equal.2
      rfl
    · intro equal
      exact ⟨congrArg RawPhase.Interval.lower equal,congrArg RawPhase.Interval.upper equal⟩)

instance rawPhaseCacheDecidableEq : DecidableEq RawPhase.Cache := by
  intro first second
  exact decidable_of_iff
    (first.qLog = second.qLog ∧ first.nextQLog = second.nextQLog ∧
      first.atOffset = second.atOffset ∧ first.atNextOffset = second.atNextOffset) (by
    constructor
    · intro equal
      cases first
      cases second
      cases equal.1
      cases equal.2.1
      cases equal.2.2.1
      cases equal.2.2.2
      rfl
    · intro equal
      exact ⟨congrArg RawPhase.Cache.qLog equal,congrArg RawPhase.Cache.nextQLog equal,
        congrArg RawPhase.Cache.atOffset equal,congrArg RawPhase.Cache.atNextOffset equal⟩)

/-- The computational predicate is exactly the existing cached-table check. -/
def tableCheck (cell : RawPhase.Cell) (sources : Array RawPhase.Geometry)
    (caches : Array RawPhase.Cache) : Bool :=
  sources.all (fun geometry => decide (finitePhaseAnalyticChecked cell geometry)) &&
    decide (caches = sources.map (finitePhaseCache cell))

end LambdaCantor.RationalPowers.RawLog
