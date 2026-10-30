import LambdaCantor.RationalPowers.LargeExponentRawBatchCore

namespace LambdaCantor.RationalPowers.RawLiteralCodec

/-- The 64 ASCII digits are 0-9, A-Z, a-z, -, _.  Delimiters are comma
and semicolon. This decoder changes only the representation of literal data. -/
def digit (character : Char) : Nat :=
  if '0' ≤ character ∧ character ≤ '9' then character.toNat - '0'.toNat
  else if 'A' ≤ character ∧ character ≤ 'Z' then character.toNat - 'A'.toNat + 10
  else if 'a' ≤ character ∧ character ≤ 'z' then character.toNat - 'a'.toNat + 36
  else if character = '-' then 62
  else 63

/-- Ten initial fields, followed by every original encoded arc in original order.
Malformed short rows have a fixed total fallback; the concrete full-data equality
is a separate required proof and does not assume validity of the encoding. -/
def record (reversedFields : List Nat) : RawPhase.CachedCell :=
  match reversedFields.reverse with
  | m :: endpointDepth :: height :: verticalDepth :: endpoint :: denominator ::
      lower :: upper :: multiplier :: phaseDenominator :: arcs =>
    ⟨⟨m, endpointDepth, height, verticalDepth, endpoint, denominator, lower, upper⟩,
      multiplier, phaseDenominator, arcs.map RawPhase.decodeArc⟩
  | _ => ⟨⟨0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 0, []⟩

structure State where
  value : Nat := 0
  reversedFields : List Nat := []
  reversedCells : List RawPhase.CachedCell := []

def step (state : State) (character : Char) : State :=
  if character = ',' then
    { state with value := 0, reversedFields := state.value :: state.reversedFields }
  else if character = ';' then
    { value := 0, reversedFields := [],
      reversedCells := record (state.value :: state.reversedFields) :: state.reversedCells }
  else
    { state with value := 64 * state.value + digit character }

/-- Chunk boundaries need not coincide with records or numbers. String.foldl
streams UTF-8 characters without constructing a Char list or substrings. -/
def decode (chunks : List String) : List RawPhase.CachedCell :=
  ((chunks.foldl (fun state chunk => chunk.foldl step state) ({} : State)).reversedCells).reverse

end LambdaCantor.RationalPowers.RawLiteralCodec
