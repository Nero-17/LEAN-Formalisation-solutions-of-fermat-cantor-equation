import LambdaCantor.Integer.TailPhaseChecker

namespace LambdaCantor.Integer

structure FinitePhaseCell where
  m : ℕ
  endpointDepth : ℕ
  height : ℕ
  verticalDepth : ℕ
  endpoint : ℕ
  denominator : ℕ
  lower : ℕ
  upper : ℕ
  deriving DecidableEq, Inhabited

def finitePhaseCenter (cell : FinitePhaseCell) : ℕ := cell.endpoint*3^(cell.m-cell.endpointDepth)

def finitePhaseLength (cell : FinitePhaseCell) (geometry : TailPhaseGeometry) : ℕ :=
  3^(geometry.p-cell.height)

def finitePhaseBand (band : Fin 14) : ℕ × ℕ × ℕ × ℕ :=
  match band.val with
  | 0 => (11,9,2027,1624)
  | 1 => (11,7,21,11)
  | 2 => (89,73,171,137)
  | 3 => (101,79,183,143)
  | 4 => (89,57,171,89)
  | 5 => (143,61,237,101)
  | 6 => (137,57,219,89)
  | 7 => (1624,2027,9,11)
  | 8 => (11,21,7,11)
  | 9 => (137,171,73,89)
  | 10 => (143,183,79,101)
  | 11 => (89,171,57,89)
  | 12 => (101,237,61,143)
  | _ => (89,219,57,137)

def FinitePhaseCell.Checked (cell : FinitePhaseCell) : Prop :=
  cell.endpointDepth+cell.height ≤ cell.m ∧ 0 < cell.endpoint ∧
  ternaryPrefix cell.endpoint cell.endpointDepth = true ∧
  0 < cell.denominator ∧ cell.denominator ≤ cell.lower ∧
  cell.lower < cell.upper ∧ cell.upper ≤ 3*cell.denominator

instance (cell : FinitePhaseCell) : Decidable cell.Checked := by
  unfold FinitePhaseCell.Checked
  infer_instance

def finitePhaseGeometryChecked (cell : FinitePhaseCell) (geometry : TailPhaseGeometry)
    (band : Fin 14) : Prop :=
  cell.height ≤ geometry.p ∧ ternaryPrefix geometry.a geometry.p = true ∧
  geometry.a+1 ≤ 3^geometry.p ∧
  ternaryPrefix geometry.q (cell.verticalDepth+1) = true ∧
  2*3^cell.verticalDepth ≤ geometry.q ∧ geometry.q+1 ≤ 3^(cell.verticalDepth+1) ∧
  (finitePhaseBand band).1*cell.denominator*
      (finitePhaseCenter cell*finitePhaseLength cell geometry+geometry.a+1) <
    (finitePhaseBand band).2.1*cell.lower*geometry.q*3^cell.m ∧
  (finitePhaseBand band).2.2.2*cell.upper*(geometry.q+1)*3^cell.m <
    (finitePhaseBand band).2.2.1*cell.denominator*
      (finitePhaseCenter cell*finitePhaseLength cell geometry+geometry.a)

instance (cell : FinitePhaseCell) (geometry : TailPhaseGeometry) (band : Fin 14) :
    Decidable (finitePhaseGeometryChecked cell geometry band) := by
  unfold finitePhaseGeometryChecked
  infer_instance

def finitePhaseOffsetInterval (cell : FinitePhaseCell) (geometry : TailPhaseGeometry)
    (offset : ℕ) : IntInterval :=
  logRatioLatticeInterval (2^256) (2^80*3^cell.m)
    (2*finitePhaseCenter cell*finitePhaseLength cell geometry+3^cell.height*finitePhaseLength cell geometry)
    (2*finitePhaseCenter cell*finitePhaseLength cell geometry+2*offset) 12

def finitePhaseCache (cell : FinitePhaseCell) (geometry : TailPhaseGeometry) : TailPhaseCache :=
  { qLog := logRatioLatticeInterval (2^256) (2^80) geometry.q (3^(cell.verticalDepth+1)) 80
    nextQLog := logRatioLatticeInterval (2^256) (2^80) (geometry.q+1) (3^(cell.verticalDepth+1)) 80
    atOffset := finitePhaseOffsetInterval cell geometry geometry.a
    atNextOffset := finitePhaseOffsetInterval cell geometry (geometry.a+1) }

def finitePhaseAnalyticChecked (cell : FinitePhaseCell) (geometry : TailPhaseGeometry) : Prop :=
  LogRatioChecked (2^256) geometry.q (3^(cell.verticalDepth+1)) ∧
  LogRatioChecked (2^256) (geometry.q+1) (3^(cell.verticalDepth+1)) ∧
  LogRatioChecked (2^256)
    (2*finitePhaseCenter cell*finitePhaseLength cell geometry+3^cell.height*finitePhaseLength cell geometry)
    (2*finitePhaseCenter cell*finitePhaseLength cell geometry+2*geometry.a) ∧
  LogRatioChecked (2^256)
    (2*finitePhaseCenter cell*finitePhaseLength cell geometry+3^cell.height*finitePhaseLength cell geometry)
    (2*finitePhaseCenter cell*finitePhaseLength cell geometry+2*(geometry.a+1))

instance (cell : FinitePhaseCell) (geometry : TailPhaseGeometry) :
    Decidable (finitePhaseAnalyticChecked cell geometry) := by
  unfold finitePhaseAnalyticChecked
  infer_instance

structure FinitePhaseArc where
  sourceIndex : ℕ
  shift : ℤ
  band : Fin 14
  deriving DecidableEq, Inhabited

def finitePhaseInset (cell : FinitePhaseCell) : ℤ := (cell.denominator*2^80 : ℤ)/10^12+1

def finitePhaseLower (cell : FinitePhaseCell) (cache : TailPhaseCache) : ℤ :=
  cell.denominator*cache.qLog.upper+
    (if 0 ≤ cache.atNextOffset.upper then (cell.upper : ℤ) else cell.lower)*cache.atNextOffset.upper+
      finitePhaseInset cell

def finitePhaseUpper (cell : FinitePhaseCell) (cache : TailPhaseCache) : ℤ :=
  cell.denominator*cache.nextQLog.lower+
    (if 0 ≤ cache.atOffset.lower then (cell.lower : ℤ) else cell.upper)*cache.atOffset.lower-
      finitePhaseInset cell

def finitePhaseRow (cell : FinitePhaseCell) (cache : TailPhaseCache)
    (arc : FinitePhaseArc) : PhaseCoverRow :=
  let denominator : ℤ := cell.denominator*2^80
  { sourceIndex := arc.sourceIndex
    lower := max 0 (finitePhaseLower cell cache-arc.shift*denominator)
    upper := min denominator (finitePhaseUpper cell cache-arc.shift*denominator)
    shift := arc.shift }

def finitePhaseCellCheck (cell : FinitePhaseCell) (sources : Array TailPhaseGeometry)
    (arcs : List FinitePhaseArc) : Bool :=
  let caches := sources.map (finitePhaseCache cell)
  decide cell.Checked &&
  sources.all (fun geometry => decide (finitePhaseAnalyticChecked cell geometry)) &&
  arcs.all (fun arc => decide (arc.sourceIndex < sources.size ∧
    finitePhaseGeometryChecked cell sources[arc.sourceIndex]! arc.band)) &&
  phaseCoverCheck (cell.denominator*2^80)
    (arcs.map (fun arc => finitePhaseRow cell caches[arc.sourceIndex]! arc))

end LambdaCantor.Integer
