import LambdaCantor.RationalPowers.SharedLogCatalogueTypes
import LambdaCantor.RationalPowers.IdentifierLookup

namespace LambdaCantor.RationalPowers

/-- Bounds are checked before either array access. No default source can
silently stand for a missing module or row. -/
def ordinaryReferenceLookup (blocks : Array SharedSourceBlock) (reference : OrdinaryReference) :
    Option (SharedSourceBlock × SharedLogRow) :=
  if block_bound : reference.block < blocks.size then
    let block := blocks[reference.block]
    if row_bound : reference.row < block.rows.size then
      some (block, block.rows[reference.row])
    else none
  else none

theorem ordinaryReferenceLookup_mem (blocks : Array SharedSourceBlock) (reference : OrdinaryReference)
    (block : SharedSourceBlock) (row : SharedLogRow)
    (found : ordinaryReferenceLookup blocks reference = some (block,row)) :
    block ∈ blocks ∧ row ∈ block.rows := by
  unfold ordinaryReferenceLookup at found
  split at found
  next block_bound =>
    dsimp only at found
    split at found
    next row_bound =>
      have equality := Option.some.inj found
      have block_equal := congrArg Prod.fst equality
      have row_equal := congrArg Prod.snd equality
      dsimp only at block_equal row_equal
      subst block
      subst row
      exact ⟨Array.getElem_mem .., Array.getElem_mem ..⟩
    next => simp only [reduceCtorEq] at found
  next => simp only [reduceCtorEq] at found

/-- This is the actual binary identifier lookup followed by bounded module
and row access. The key is still compared with the returned row's own index. -/
def ordinarySourceLookup (blocks : Array SharedSourceBlock)
    (entries : Array (IdentifierEntry OrdinaryReference)) (identifier : ℕ) :
    Option (SharedSourceBlock × SharedLogRow) :=
  match identifierLookup entries identifier with
  | none => none
  | some entry => ordinaryReferenceLookup blocks entry.payload

def ordinaryIdentifierAccepted (blocks : Array SharedSourceBlock)
    (entries : Array (IdentifierEntry OrdinaryReference)) (identifier : ℕ) : Bool :=
  match ordinarySourceLookup blocks entries identifier with
  | none => false
  | some (_,row) => decide (row.lowIndex = identifier ∧ row.IndexMatches)

end LambdaCantor.RationalPowers
