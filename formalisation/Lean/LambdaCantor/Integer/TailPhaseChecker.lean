import LambdaCantor.Integer.TailPhaseIntervalSound
import LambdaCantor.Integer.PhaseCover
import LambdaCantor.Certificates.IntegerLogSourceDefinition

namespace LambdaCantor.Integer

structure TailPhaseGeometry where
  p : ℕ
  q : ℕ
  a : ℕ
  deriving DecidableEq, Inhabited

def tailPhaseLength (geometry : TailPhaseGeometry) : ℕ := 3^(geometry.p-3)

def tailPhaseBand (band : Fin 4) : ℕ × ℕ × ℕ × ℕ :=
  match band.val with
  | 0 => (11,9,2027,1624)
  | 1 => (11,7,21,11)
  | 2 => (1624,2027,9,11)
  | _ => (11,21,7,11)

def TailPhaseGeometry.Checked (geometry : TailPhaseGeometry) (cell : ℕ) (band : Fin 4) : Prop :=
  5 ≤ geometry.p ∧ geometry.p ≤ 10 ∧
  ternaryPrefix geometry.a geometry.p = true ∧ geometry.a+1 ≤ 3^geometry.p ∧
  ternaryPrefix geometry.q 5 = true ∧ 162 ≤ geometry.q ∧ geometry.q+1 ≤ 243 ∧
  0 < cell ∧
  (tailPhaseBand band).1 * 4000 * (1180980*tailPhaseLength geometry+geometry.a+1) <
    (tailPhaseBand band).2.1*(2*cell-1)*geometry.q*1180980 ∧
  (tailPhaseBand band).2.2.2*(2*cell+1)*(geometry.q+1) <
    (tailPhaseBand band).2.2.1*4000*tailPhaseLength geometry

instance (geometry : TailPhaseGeometry) (cell : ℕ) (band : Fin 4) :
    Decidable (geometry.Checked cell band) := by
  unfold TailPhaseGeometry.Checked
  infer_instance

structure TailPhaseCache where
  qLog : IntInterval
  nextQLog : IntInterval
  atOffset : IntInterval
  atNextOffset : IntInterval
  deriving Inhabited

def tailPhaseCache (geometry : TailPhaseGeometry) : TailPhaseCache :=
  { qLog := logRatioLatticeInterval (2^256) (2^80) geometry.q 243 80
    nextQLog := logRatioLatticeInterval (2^256) (2^80) (geometry.q+1) 243 80
    atOffset := tailPhaseInterval (2^256) (2^80) 1180980 (tailPhaseLength geometry) geometry.a
    atNextOffset := tailPhaseInterval (2^256) (2^80) 1180980 (tailPhaseLength geometry) (geometry.a+1) }

def TailPhaseGeometry.AnalyticChecked (geometry : TailPhaseGeometry) : Prop :=
  LogRatioChecked (2^256) geometry.q 243 ∧
  LogRatioChecked (2^256) (geometry.q+1) 243 ∧
  TailPhaseChecked (2^256) (2^80) 1180980 (tailPhaseLength geometry) geometry.a ∧
  TailPhaseChecked (2^256) (2^80) 1180980 (tailPhaseLength geometry) (geometry.a+1)

instance (geometry : TailPhaseGeometry) : Decidable geometry.AnalyticChecked := by
  unfold TailPhaseGeometry.AnalyticChecked
  infer_instance

def tailPhaseInset : ℤ := (4000*(2^80 : ℤ))/10^12+1

def tailPhaseLower (cell : ℕ) (cache : TailPhaseCache) : ℤ :=
  4000*cache.qLog.upper+
    (if 0 ≤ cache.atNextOffset.upper then 2*(cell : ℤ)+1 else 2*cell-1)*cache.atNextOffset.upper+
      tailPhaseInset

def tailPhaseUpper (cell : ℕ) (cache : TailPhaseCache) : ℤ :=
  4000*cache.nextQLog.lower+
    (if 0 ≤ cache.atOffset.lower then 2*(cell : ℤ)-1 else 2*cell+1)*cache.atOffset.lower-
      tailPhaseInset

structure TailPhaseArc where
  sourceIndex : ℕ
  shift : ℤ
  band : Fin 4
  deriving DecidableEq, Inhabited

def tailPhaseRow (cell : ℕ) (cache : TailPhaseCache) (arc : TailPhaseArc) : PhaseCoverRow :=
  { sourceIndex := arc.sourceIndex
    lower := max 0 (tailPhaseLower cell cache-arc.shift*(4000*2^80))
    upper := min (4000*2^80) (tailPhaseUpper cell cache-arc.shift*(4000*2^80))
    shift := arc.shift }

def tailPhaseCellCoreCheck (sources : Array TailPhaseGeometry) (caches : Array TailPhaseCache) (cell : ℕ)
    (arcs : List TailPhaseArc) : Bool :=
  arcs.all (fun arc => decide (arc.sourceIndex < sources.size ∧
    (sources[arc.sourceIndex]!).Checked cell arc.band)) &&
  phaseCoverCheck (4000*2^80) (arcs.map (fun arc => tailPhaseRow cell caches[arc.sourceIndex]! arc))

def tailPhaseCellCheck (sources : Array TailPhaseGeometry) (cell : ℕ)
    (arcs : List TailPhaseArc) : Bool :=
  sources.all (fun geometry => decide geometry.AnalyticChecked) &&
    tailPhaseCellCoreCheck sources (sources.map tailPhaseCache) cell arcs

/-- The expensive outward logarithms are computed once per geometry table,
not once for every coefficient cell that reuses the table. -/
def tailPhaseBatchCheck (sources : Array TailPhaseGeometry) (cells : List (ℕ × List TailPhaseArc)) : Bool :=
  let caches := sources.map tailPhaseCache
  sources.all (fun geometry => decide geometry.AnalyticChecked) &&
    cells.all (fun cell => tailPhaseCellCoreCheck sources caches cell.1 cell.2)

theorem tailPhaseBatchCheck_cell (sources : Array TailPhaseGeometry)
    (cells : List (ℕ × List TailPhaseArc)) (checked : tailPhaseBatchCheck sources cells = true)
    (cell : ℕ × List TailPhaseArc) (member : cell ∈ cells) :
    tailPhaseCellCheck sources cell.1 cell.2 = true := by
  simp only [tailPhaseBatchCheck,Bool.and_eq_true] at checked
  simp only [tailPhaseCellCheck,Bool.and_eq_true]
  exact ⟨checked.1,(List.all_eq_true.mp checked.2) cell member⟩

end LambdaCantor.Integer
