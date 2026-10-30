import LambdaCantor.RationalPowers.CompactLow.Keys

namespace LambdaCantor.RationalPowers.CompactLow

/-- Binary search consults keys only; no sortedness assumption is needed here. -/
theorem lookupLoop_forget {Payload : Type} (source : Array (IdentifierEntry Payload))
    (identifier lower upper fuel : Nat) :
    identifierLookupLoop (source.map forgetPayload) identifier lower upper fuel =
      (identifierLookupLoop source identifier lower upper fuel).map forgetPayload := by
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel inductionHypothesis =>
    by_cases ordered : lower < upper
    · by_cases bound : (lower+upper)/2 < source.size
      · by_cases equal : identifier = source[(lower+upper)/2].identifier
        · simp only [identifierLookupLoop, Array.size_map, ordered, if_true,
            dif_pos bound, Array.getElem_map, forgetPayload, equal, Option.map]
        · by_cases before : identifier < source[(lower+upper)/2].identifier
          · simpa only [identifierLookupLoop, Array.size_map, ordered, if_true,
              dif_pos bound, Array.getElem_map, forgetPayload, equal, if_false,
              before, Option.map] using inductionHypothesis lower ((lower+upper)/2)
          · simpa only [identifierLookupLoop, Array.size_map, ordered, if_true,
              dif_pos bound, Array.getElem_map, forgetPayload, equal, if_false,
              before, Option.map] using inductionHypothesis ((lower+upper)/2+1) upper
      · simp only [identifierLookupLoop, Array.size_map, ordered, if_true,
          dif_neg bound, Option.map]
    · simp only [identifierLookupLoop, Array.size_map, ordered, if_false, Option.map]

theorem lookup_forget {Payload : Type} (source : Array (IdentifierEntry Payload))
    (identifier : Nat) :
    identifierLookup (source.map forgetPayload) identifier =
      (identifierLookup source identifier).map forgetPayload := by
  unfold identifierLookup
  simp only [Array.size_map]
  exact lookupLoop_forget source identifier 0 source.size (source.size+1)

end LambdaCantor.RationalPowers.CompactLow

#print axioms LambdaCantor.RationalPowers.CompactLow.lookup_forget
