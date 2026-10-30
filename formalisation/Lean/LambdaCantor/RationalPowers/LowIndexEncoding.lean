import LambdaCantor.RationalPowers.LowDenominatorIndex

namespace LambdaCantor.RationalPowers

/-- Native classification uses constant-time array access to the already
verified residue table, rather than a repeated linear List.get traversal. -/
def lowResidueArray : Array (ℕ × ℕ) := lowResiduePairs.toArray

def lowRationalPairAt (integerPart residue : ℕ) : ℕ × ℕ :=
  let pair := lowResidueArray.getD residue (0,0)
  (pair.1*(integerPart+1)+pair.2,pair.1)

theorem lowRationalPairAt_index (index : LowRationalIndex) :
    lowRationalPairAt index.1.val index.2.val =
      (lowRationalNumerator index,lowRationalDenominator index) := by
  have bound : index.2.val < lowResidueArray.size := by
    simpa only [lowResidueArray, List.size_toArray] using index.2.isLt
  have table_value : lowResidueArray.getD index.2.val (0,0) = lowResiduePairs.get index.2 := by
    rw [← Array.getElem_eq_getD (h := bound) (0,0)]
    simp only [lowResidueArray, List.getElem_toArray, List.get_eq_getElem]
  simp only [lowRationalPairAt, table_value, lowRationalNumerator, lowRationalDenominator]

/-- The same row-major identifier is used by the finite classifier and every
ordinary, coarse and exceptional source lookup. -/
def lowRationalIdentifier (index : LowRationalIndex) : ℕ :=
  index.1.val*3675+index.2.val

theorem lowRationalIdentifier_lt (index : LowRationalIndex) : lowRationalIdentifier index < 8033550 := by
  have integer_bound := index.1.isLt
  have residue_bound : index.2.val < 3675 := by
    simpa only [lowResiduePairs_length] using index.2.isLt
  unfold lowRationalIdentifier
  omega

def lowRationalIndexFromIdentifier (identifier : ℕ) (bound : identifier < 8033550) : LowRationalIndex :=
  (⟨identifier/3675, by omega⟩,
    ⟨identifier%3675, by rw [lowResiduePairs_length]; omega⟩)

theorem lowRationalIdentifier_decode (identifier : ℕ) (bound : identifier < 8033550) :
    lowRationalIdentifier (lowRationalIndexFromIdentifier identifier bound) = identifier := by
  dsimp only [lowRationalIdentifier, lowRationalIndexFromIdentifier]
  exact Nat.div_add_mod' identifier 3675

theorem lowRationalIndex_decode_identifier (index : LowRationalIndex) :
    lowRationalIndexFromIdentifier (lowRationalIdentifier index) (lowRationalIdentifier_lt index) = index := by
  have residue_bound : index.2.val < 3675 := by
    simpa only [lowResiduePairs_length] using index.2.isLt
  apply Prod.ext <;> apply Fin.ext
  · dsimp only [lowRationalIndexFromIdentifier, lowRationalIdentifier]
    omega
  · dsimp only [lowRationalIndexFromIdentifier, lowRationalIdentifier]
    omega

theorem lowRationalIdentifier_injective : Function.Injective lowRationalIdentifier := by
  intro first second equality
  have decoded := congrArg (fun identifier =>
    if bound : identifier < 8033550 then some (lowRationalIndexFromIdentifier identifier bound) else none) equality
  simpa only [dif_pos (lowRationalIdentifier_lt first), dif_pos (lowRationalIdentifier_lt second),
    lowRationalIndex_decode_identifier, Option.some.injEq] using decoded

/-- The native pair decoder agrees with the exact indexed fraction at the
row-major identifier, including both quotient and remainder coordinates. -/
theorem lowRationalPairAt_identifier (index : LowRationalIndex) :
    lowRationalPairAt (lowRationalIdentifier index/3675) (lowRationalIdentifier index%3675) =
      (lowRationalNumerator index,lowRationalDenominator index) := by
  have decoded := lowRationalIndex_decode_identifier index
  have integerPart := congrArg (fun value : LowRationalIndex => value.1.val) decoded
  have residue := congrArg (fun value : LowRationalIndex => value.2.val) decoded
  change lowRationalIdentifier index/3675 = index.1.val at integerPart
  change lowRationalIdentifier index%3675 = index.2.val at residue
  rw [integerPart, residue, lowRationalPairAt_index]

end LambdaCantor.RationalPowers
