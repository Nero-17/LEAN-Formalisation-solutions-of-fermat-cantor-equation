import LambdaCantor.RationalPowers.LargeExponentCheapGrid

namespace LambdaCantor.RationalPowers.RawPhase

structure Cell where
  m : Nat
  endpointDepth : Nat
  height : Nat
  verticalDepth : Nat
  endpoint : Nat
  denominator : Nat
  lower : Nat
  upper : Nat
  deriving Inhabited

structure Geometry where
  p : Nat
  q : Nat
  a : Nat
  deriving Inhabited

structure Interval where
  lower : Int
  upper : Int
  deriving Inhabited

structure Cache where
  qLog : Interval
  nextQLog : Interval
  atOffset : Interval
  atNextOffset : Interval
  deriving Inhabited

structure Arc where
  sourceIndex : Nat
  shift : Int
  band : Fin 14
  deriving Inhabited

def decodeArc (encoded : Nat) : Arc :=
  let rotation := encoded / 4294967296 % 4294967296
  ⟨encoded % 4294967296,
    if rotation % 2 = 0 then (rotation / 2 : Nat) else -((rotation / 2 : Nat) : Int)-1,
    ⟨encoded / 18446744073709551616 % 14, Nat.mod_lt _ (by decide)⟩⟩

def ternaryPrefix : Nat → Nat → Bool
  | word, 0 => word == 0
  | word, depth+1 =>
      (word % 3 == 0 || word % 3 == 2) && ternaryPrefix (word/3) depth

def Cell.Checked (cell : Cell) : Prop :=
  cell.endpointDepth+cell.height ≤ cell.m ∧ 0 < cell.endpoint ∧
  ternaryPrefix cell.endpoint cell.endpointDepth = true ∧
  0 < cell.denominator ∧ cell.denominator ≤ cell.lower ∧
  cell.lower < cell.upper ∧ cell.upper ≤ 3*cell.denominator

instance (cell : Cell) : Decidable cell.Checked := by
  unfold Cell.Checked
  infer_instance

def center (cell : Cell) : Nat := cell.endpoint*3^(cell.m-cell.endpointDepth)
def length (cell : Cell) (geometry : Geometry) : Nat := 3^(geometry.p-cell.height)

def band (band : Fin 14) : Nat × Nat × Nat × Nat :=
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

def geometryChecked (cell : Cell) (geometry : Geometry) (slopeBand : Fin 14) : Prop :=
  cell.height ≤ geometry.p ∧ ternaryPrefix geometry.a geometry.p = true ∧
  geometry.a+1 ≤ 3^geometry.p ∧
  ternaryPrefix geometry.q (cell.verticalDepth+1) = true ∧
  2*3^cell.verticalDepth ≤ geometry.q ∧ geometry.q+1 ≤ 3^(cell.verticalDepth+1) ∧
  (band slopeBand).1*cell.denominator*(center cell*length cell geometry+geometry.a+1) <
    (band slopeBand).2.1*cell.lower*geometry.q*3^cell.m ∧
  (band slopeBand).2.2.2*cell.upper*(geometry.q+1)*3^cell.m <
    (band slopeBand).2.2.1*cell.denominator*(center cell*length cell geometry+geometry.a)

instance (cell : Cell) (geometry : Geometry) (slopeBand : Fin 14) :
    Decidable (geometryChecked cell geometry slopeBand) := by
  unfold geometryChecked
  infer_instance

def inset (cell : Cell) : Int := (cell.denominator*2^80 : Int)/10^12+1

def lower (cell : Cell) (cache : Cache) : Int :=
  cell.denominator*cache.qLog.upper+
    (if 0 ≤ cache.atNextOffset.upper then (cell.upper : Int) else cell.lower)*cache.atNextOffset.upper+
      inset cell

def upper (cell : Cell) (cache : Cache) : Int :=
  cell.denominator*cache.nextQLog.lower+
    (if 0 ≤ cache.atOffset.lower then (cell.lower : Int) else cell.upper)*cache.atOffset.lower-
      inset cell

def phaseInterval (denominator : Nat) (cell : Cell) (cache : Cache) (arc : Arc) : Int × Int :=
  (max 0 ((denominator : Int)*lower cell cache-arc.shift*(cell.denominator*2^80)),
   min (cell.denominator*2^80) ((denominator : Int)*upper cell cache-arc.shift*(cell.denominator*2^80)))

def coreCheck (denominator : Nat) (cell : Cell) (sources : Array Geometry)
    (caches : Array Cache) (arcs : List Arc) : Bool :=
  arcs.all (fun arc => decide (arc.sourceIndex < sources.size ∧
    geometryChecked cell sources[arc.sourceIndex]! arc.band)) &&
  (CheapGrid.intervalScan (arcs.map (fun arc => phaseInterval denominator cell caches[arc.sourceIndex]! arc))
      0 (cell.denominator*2^80) &&
    arcs.any (fun arc => decide ((phaseInterval denominator cell caches[arc.sourceIndex]! arc).1 ≤ 0 ∧
      0 ≤ (phaseInterval denominator cell caches[arc.sourceIndex]! arc).2)))

end LambdaCantor.RationalPowers.RawPhase
