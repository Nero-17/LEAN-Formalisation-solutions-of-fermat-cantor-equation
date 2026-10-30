import LambdaCantor.RationalPowers.LowPartitionData.Definitions
import LambdaCantor.RationalPowers.CompactLow.Keys
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers.CompactLow
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Validate every original reference directly, without assuming a sort theorem. -/
def referenceAccepted (entry : IdentifierEntry OrdinaryReference) : Bool :=
  match ordinaryReferenceLookup sharedFullSourceBlocks entry.payload with
  | none => false
  | some (_, row) => decide (row.lowIndex = entry.identifier ∧ row.IndexMatches)

/-- Both the complete sorted key projection and all original payload references. -/
def validation : Bool :=
  decide (entries = sharedFullOrdinaryEntries.map forgetPayload) &&
    sharedFullOrdinaryEntries.all referenceAccepted

theorem data_checked : validation = true := by
  native_decide

end LambdaCantor.RationalPowers.CompactLow
