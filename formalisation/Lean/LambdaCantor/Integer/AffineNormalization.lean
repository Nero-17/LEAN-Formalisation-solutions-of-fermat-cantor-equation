import LambdaCantor.Integer.AffineAddressBranching

namespace LambdaCantor.Integer

def addressShift (depth : ℕ) (digits : ℕ → Bool × Bool) : ℕ → Bool × Bool :=
  fun j => digits (j+depth)

noncomputable def normalizedAffineLevel (r : ℝ) (digits : ℕ → Bool × Bool) (depth : ℕ) : ℝ :=
  (r*(pairedAddress (addressShift depth digits)).1+
    (pairedAddress (addressShift depth digits)).2)/2

theorem shared_prefix_normalized_level (r level : ℝ) (reference digits : ℕ → Bool × Bool)
    (referenceMember : reference ∈ affineAddressFibre r level)
    (member : digits ∈ affineAddressFibre r level) (depth : ℕ)
    (agreement : ∀ j < depth, digits j=reference j) :
    addressShift depth digits ∈ affineAddressFibre r (normalizedAffineLevel r reference depth) := by
  have firstPrefix : prefixValue (1/3) (fun j => (digits j).1) depth =
      prefixValue (1/3) (fun j => (reference j).1) depth := by
    unfold prefixValue
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only
    exact congrArg (fun value : Bool × Bool =>
      (if value.1 then (1 : ℝ) else 0)*(1/3 : ℝ)^j)
      (agreement j (Finset.mem_range.mp hj))
  have secondPrefix : prefixValue (1/3) (fun j => (digits j).2) depth =
      prefixValue (1/3) (fun j => (reference j).2) depth := by
    unfold prefixValue
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only
    exact congrArg (fun value : Bool × Bool =>
      (if value.2 then (1 : ℝ) else 0)*(1/3 : ℝ)^j)
      (agreement j (Finset.mem_range.mp hj))
  have source : (r*(pairedAddress digits).1+(pairedAddress digits).2)/2 =
      (r*(pairedAddress reference).1+(pairedAddress reference).2)/2 :=
    member.2.trans referenceMember.2.symm
  change pairedAddress (addressShift depth digits) ∈
    affineFibre r (normalizedAffineLevel r reference depth)
  constructor
  · constructor <;> rw [← cantorSet_third_eq] <;> exact ⟨_,rfl⟩
  · apply (mul_left_cancel₀ (by positivity : (1/3 : ℝ)^depth ≠ 0))
    unfold pairedAddress at source
    dsimp only at source
    rw [address_prefix_tail (by norm_num) (by norm_num) (fun j => (digits j).1) depth,
      address_prefix_tail (by norm_num) (by norm_num) (fun j => (digits j).2) depth,
      address_prefix_tail (by norm_num) (by norm_num) (fun j => (reference j).1) depth,
      address_prefix_tail (by norm_num) (by norm_num) (fun j => (reference j).2) depth,
      firstPrefix,secondPrefix] at source
    change (1/3 : ℝ)^depth *
      ((r*address (1/3) (fun j => (digits (j+depth)).1)+
        address (1/3) (fun j => (digits (j+depth)).2))/2) =
      (1/3 : ℝ)^depth *
      ((r*address (1/3) (fun j => (reference (j+depth)).1)+
        address (1/3) (fun j => (reference (j+depth)).2))/2)
    nlinarith [source]

theorem shift_injective_on_prefix (reference : ℕ → Bool × Bool) (depth : ℕ) :
    Set.InjOn (addressShift depth)
      (prefixCylinder ⟨depth,fun j => reference j.val⟩) := by
  intro first firstMember second secondMember equal
  funext j
  by_cases before : j < depth
  · exact (firstMember ⟨j,before⟩).trans (secondMember ⟨j,before⟩).symm
  · have shifted := congrFun equal (j-depth)
    simpa only [addressShift,Nat.sub_add_cancel (le_of_not_gt before)] using shifted

/-- Normalizing an uncountable prefix slice preserves uncountability of the
actual affine fibre. Injectivity on the fixed prefix prevents loss of cardinality. -/
theorem uncountable_normalized_fibre (r level : ℝ) (reference : ℕ → Bool × Bool)
    (referenceMember : reference ∈ affineAddressFibre r level) (depth : ℕ)
    (uncountable : ¬ (affineAddressFibre r level ∩
      prefixCylinder ⟨depth,fun j => reference j.val⟩).Countable) :
    ¬ (affineFibre r (normalizedAffineLevel r reference depth)).Countable := by
  intro countable
  have addressCountable : (affineAddressFibre r (normalizedAffineLevel r reference depth)).Countable :=
    countable.preimage pairedAddress_injective
  apply uncountable
  apply Set.MapsTo.countable_of_injOn (f := addressShift depth) ?_ ?_ addressCountable
  · intro digits member
    apply shared_prefix_normalized_level r level reference digits referenceMember member.1 depth
    intro j hj
    exact member.2 ⟨j,hj⟩
  · intro first firstMember second secondMember equal
    exact shift_injective_on_prefix reference depth firstMember.2 secondMember.2 equal

/-- Every uncountable affine fibre has a descendant whose normalized level
lies in an open switch overlap. Endpoint fibres are countable, so selecting
two uncountable children gives strictness on both sides. -/
theorem uncountable_fibre_strict_descendant (r level : ℝ) (positive : 1 < r)
    (uncountable : ¬ (affineFibre r level).Countable) :
    ∃ digits ∈ affineAddressFibre r level, ∃ depth : ℕ,
      normalizedAffineLevel r digits depth ∈ strictSwitchSet r := by
  obtain ⟨left,leftMember,right,rightMember,depth,agreement,different,
    leftUncountable,rightUncountable⟩ := uncountable_addresses_branch
      (affineAddressFibre r level) (affineAddressFibre_uncountable r level uncountable)
  have leftStrict := uncountable_affine_level_strict r _ (by linarith)
    (uncountable_normalized_fibre r level left leftMember (depth+1) leftUncountable)
  have rightStrict := uncountable_affine_level_strict r _ (by linarith)
    (uncountable_normalized_fibre r level right rightMember (depth+1) rightUncountable)
  have parentEqual : normalizedAffineLevel r right depth=normalizedAffineLevel r left depth :=
    (shared_prefix_normalized_level r level left right leftMember rightMember depth
      (fun j hj => (agreement j hj).symm)).2
  have leftStep := affineTail_step r (fun j => (left j).1) (fun j => (left j).2) depth
  have rightStep := affineTail_step r (fun j => (right j).1) (fun j => (right j).2) depth
  change normalizedAffineLevel r left (depth+1)=3*normalizedAffineLevel r left depth-
    childOffset r (digitPairLabel (left depth)) at leftStep
  change normalizedAffineLevel r right (depth+1)=3*normalizedAffineLevel r right depth-
    childOffset r (digitPairLabel (right depth)) at rightStep
  rw [parentEqual] at rightStep
  refine ⟨left,leftMember,depth, ?_⟩
  apply strict_branching_in_switch r _ positive
    (digitPairLabel (left depth)) (digitPairLabel (right depth))
  · exact fun equal => different (digitPairLabel_injective equal)
  · constructor <;> linarith [leftStrict.1,leftStrict.2]
  · constructor <;> linarith [rightStrict.1,rightStrict.2]

end LambdaCantor.Integer
