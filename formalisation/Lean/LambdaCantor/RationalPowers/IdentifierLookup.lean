import Mathlib.Init
import Lean.Elab.Tactic.Omega

namespace LambdaCantor.RationalPowers

/-- Only lookup keys and small payload references are sorted globally. Source
rows remain grouped for logarithm locality and are never duplicated here. -/
structure IdentifierEntry (Payload : Type) where
  identifier : Nat
  payload : Payload
  deriving DecidableEq

def identifierLookupLoop {Payload : Type} (entries : Array (IdentifierEntry Payload))
    (identifier lower upper : Nat) : Nat → Option (IdentifierEntry Payload)
  | 0 => none
  | fuel+1 =>
    if lower < upper then
      let midpoint := (lower+upper)/2
      if bound : midpoint < entries.size then
        let entry := entries[midpoint]
        if identifier = entry.identifier then some entry
        else if identifier < entry.identifier then identifierLookupLoop entries identifier lower midpoint fuel
        else identifierLookupLoop entries identifier (midpoint+1) upper fuel
      else none
    else none

/-- Lookup soundness does not assume sortedness: every successful result is
an actual table entry with exactly the queried key. Sorting affects speed and
successful coverage; the separate exhaustive classifier detects missing keys. -/
theorem identifierLookupLoop_sound {Payload : Type} (entries : Array (IdentifierEntry Payload))
    (identifier lower upper fuel : Nat) (entry : IdentifierEntry Payload)
    (found : identifierLookupLoop entries identifier lower upper fuel = some entry) :
    entry ∈ entries ∧ entry.identifier = identifier := by
  induction fuel generalizing lower upper with
  | zero => simp only [identifierLookupLoop, reduceCtorEq] at found
  | succ fuel inductionHypothesis =>
    by_cases ordered : lower < upper
    · by_cases bound : (lower+upper)/2 < entries.size
      · by_cases equal : identifier = entries[(lower+upper)/2].identifier
        · have entry_equal : entries[(lower+upper)/2] = entry := by
            exact Option.some.inj (by simpa only [identifierLookupLoop, ordered, if_true, dif_pos bound,
              equal] using found)
          exact ⟨entry_equal ▸ Array.getElem_mem .., entry_equal ▸ equal.symm⟩
        · by_cases before : identifier < entries[(lower+upper)/2].identifier
          · apply inductionHypothesis lower ((lower+upper)/2)
            simpa only [identifierLookupLoop, ordered, if_true, dif_pos bound, equal, if_false, before] using found
          · apply inductionHypothesis ((lower+upper)/2+1) upper
            simpa only [identifierLookupLoop, ordered, if_true, dif_pos bound, equal, if_false, before] using found
      · simp only [identifierLookupLoop, ordered, if_true, dif_neg bound, reduceCtorEq] at found
    · simp only [identifierLookupLoop, ordered, if_false, reduceCtorEq] at found

def identifierLookup {Payload : Type} (entries : Array (IdentifierEntry Payload)) (identifier : Nat) :
    Option (IdentifierEntry Payload) :=
  identifierLookupLoop entries identifier 0 entries.size (entries.size+1)

theorem identifierLookup_sound {Payload : Type} (entries : Array (IdentifierEntry Payload))
    (identifier : Nat) (entry : IdentifierEntry Payload)
    (found : identifierLookup entries identifier = some entry) :
    entry ∈ entries ∧ entry.identifier = identifier :=
  identifierLookupLoop_sound entries identifier 0 entries.size (entries.size+1) entry found

end LambdaCantor.RationalPowers
