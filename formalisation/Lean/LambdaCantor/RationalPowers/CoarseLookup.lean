import LambdaCantor.RationalPowers.CoarseWitnessChecks
import Mathlib.Data.Nat.Log

namespace LambdaCantor.RationalPowers

/-- A retained increasing-frontier interval stores its exact rational lower
endpoint and the original source provenance. The final width and full-band
checks, rather than this endpoint, certify the selected physical source. -/
structure CoarseIntervalEntry where
  lowerNumerator : ℕ
  lowerDenominator : ℕ
  row : CoarseSourceRow
  band : ℕ
  deriving DecidableEq

/-- Strict predecessor search uses only natural cross products. Sortedness
is an efficiency/completeness property of generated data, never a soundness
axiom: the full partition rejects any index at which the returned source
fails its separate actual width or derivative-band check. -/
def coarseIntervalLookupLoop (entries : Array CoarseIntervalEntry)
    (numerator normalizedDenominator lower upper : ℕ)
    (previous : Option CoarseIntervalEntry) : ℕ → Option CoarseIntervalEntry
  | 0 => previous
  | fuel+1 =>
    if lower < upper then
      let midpoint := (lower+upper)/2
      if bound : midpoint < entries.size then
        let entry := entries[midpoint]
        if entry.lowerNumerator*normalizedDenominator < numerator*entry.lowerDenominator then
          coarseIntervalLookupLoop entries numerator normalizedDenominator (midpoint+1) upper (some entry) fuel
        else coarseIntervalLookupLoop entries numerator normalizedDenominator lower midpoint previous fuel
      else previous
    else previous

def coarseIntervalLookup (entries : Array CoarseIntervalEntry)
    (numerator normalizedDenominator : ℕ) : Option CoarseIntervalEntry :=
  coarseIntervalLookupLoop entries numerator normalizedDenominator 0 entries.size none (entries.size+1)

/-- One array per denominator, indexed directly by b. Query normalization
uses floor(log_3(floor(a/b))); exhaustive finite acceptance subsequently
checks the returned source at the original a,b and this actual shift. -/
def coarseCatalogueSelect (catalogues : Array (Array CoarseIntervalEntry))
    (identifier : ℕ) : Option CoarseWitness :=
  let pair := lowRationalPairAt (identifier/3675) (identifier%3675)
  let shift := Nat.log 3 (pair.1/pair.2)
  match coarseIntervalLookup (catalogues.getD pair.2 #[]) pair.1 (pair.2*3^shift) with
  | none => none
  | some entry => some ⟨entry.row,shift,entry.band⟩

end LambdaCantor.RationalPowers
