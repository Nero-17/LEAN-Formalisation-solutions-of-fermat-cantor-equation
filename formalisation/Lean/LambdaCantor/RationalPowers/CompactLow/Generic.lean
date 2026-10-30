import LambdaCantor.RationalPowers.LowSourceLookup
import LambdaCantor.RationalPowers.CompactLow.Lookup

namespace LambdaCantor.RationalPowers.CompactLow.Generic

def referenceAcceptedFor (blocks : Array SharedSourceBlock)
    (entry : IdentifierEntry OrdinaryReference) : Bool :=
  match ordinaryReferenceLookup blocks entry.payload with
  | none => false
  | some (_, row) => decide (row.lowIndex = entry.identifier ∧ row.IndexMatches)

/-- Keep every array symbolic during proof elaboration and kernel reduction. -/
theorem ordinary_eq_lookup_of_all
    (blocks : Array SharedSourceBlock) (source : Array (IdentifierEntry OrdinaryReference))
    (accepts : IdentifierEntry OrdinaryReference → Bool)
    (accepts_eq : accepts = referenceAcceptedFor blocks)
    (checked : source.all accepts = true) (identifier : Nat) :
    ordinaryIdentifierAccepted blocks source identifier =
      (identifierLookup source identifier).isSome := by
  have allChecked : source.all (referenceAcceptedFor blocks) = true := by
    rw [← accepts_eq]
    exact checked
  have accepted : ∀ entry ∈ source, referenceAcceptedFor blocks entry = true := by
    simpa only [Array.all_eq_true'] using allChecked
  cases found : identifierLookup source identifier with
  | none =>
    simp only [ordinaryIdentifierAccepted, ordinarySourceLookup, found, Option.isSome_none]
  | some entry =>
    have sound := identifierLookup_sound source identifier entry found
    have direct := accepted entry sound.1
    cases reference : ordinaryReferenceLookup blocks entry.payload with
    | none =>
      simp only [referenceAcceptedFor, reference] at direct
      cases direct
    | some value =>
      rcases value with ⟨block, row⟩
      simp only [referenceAcceptedFor, reference] at direct
      have properties := of_decide_eq_true direct
      have atIdentifier : ordinaryIdentifierAccepted blocks source identifier = true := by
        simp only [ordinaryIdentifierAccepted, ordinarySourceLookup, found, reference]
        exact decide_eq_true ⟨properties.1.trans sound.2, properties.2⟩
      simpa only [found, Option.isSome_some] using atIdentifier

theorem ordinary_keys_eq
    (blocks : Array SharedSourceBlock) (source : Array (IdentifierEntry OrdinaryReference))
    (keys : Array (IdentifierEntry Unit))
    (accepts : IdentifierEntry OrdinaryReference → Bool)
    (accepts_eq : accepts = referenceAcceptedFor blocks)
    (checked : source.all accepts = true)
    (keys_eq : keys = source.map forgetPayload) (identifier : Nat) :
    (identifierLookup keys identifier).isSome =
      ordinaryIdentifierAccepted blocks source identifier := by
  have projection : (identifierLookup keys identifier).isSome =
      (identifierLookup source identifier).isSome := by
    rw [keys_eq, lookup_forget]
    cases identifierLookup source identifier <;> rfl
  exact projection.trans (ordinary_eq_lookup_of_all blocks source accepts accepts_eq checked identifier).symm

end LambdaCantor.RationalPowers.CompactLow.Generic

#print axioms LambdaCantor.RationalPowers.CompactLow.Generic.ordinary_eq_lookup_of_all
#print axioms LambdaCantor.RationalPowers.CompactLow.Generic.ordinary_keys_eq
