import LambdaCantor.Integer.AffineNormalization

namespace LambdaCantor.Integer

def replacePairTail (reference continuation : ℕ → Bool × Bool) (depth : ℕ) : ℕ → Bool × Bool :=
  fun j => if j < depth then reference j else continuation (j-depth)

theorem replaced_prefix (reference continuation : ℕ → Bool × Bool) (depth j : ℕ)
    (before : j < depth) : replacePairTail reference continuation depth j=reference j := by
  simp [replacePairTail,before]

theorem replaced_shift (reference continuation : ℕ → Bool × Bool) (depth later : ℕ) :
    addressShift (depth+later) (replacePairTail reference continuation depth) =
      addressShift later continuation := by
  funext j
  have notBefore : ¬ j+(depth+later) < depth := by omega
  have index : j+(depth+later)-depth=j+later := by omega
  simp [addressShift,replacePairTail,notBefore,index]

theorem replacement_in_fibre (r level : ℝ) (reference continuation : ℕ → Bool × Bool)
    (referenceMember : reference ∈ affineAddressFibre r level) (depth : ℕ)
    (continuationMember : continuation ∈
      affineAddressFibre r (normalizedAffineLevel r reference depth)) :
    replacePairTail reference continuation depth ∈ affineAddressFibre r level := by
  have firstPrefix : prefixValue (1/3)
      (fun j => (replacePairTail reference continuation depth j).1) depth =
      prefixValue (1/3) (fun j => (reference j).1) depth := by
    unfold prefixValue
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only
    exact congrArg (fun value : Bool × Bool =>
      (if value.1 then (1 : ℝ) else 0)*(1/3 : ℝ)^j)
      (replaced_prefix reference continuation depth j (Finset.mem_range.mp hj))
  have secondPrefix : prefixValue (1/3)
      (fun j => (replacePairTail reference continuation depth j).2) depth =
      prefixValue (1/3) (fun j => (reference j).2) depth := by
    unfold prefixValue
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only
    exact congrArg (fun value : Bool × Bool =>
      (if value.2 then (1 : ℝ) else 0)*(1/3 : ℝ)^j)
      (replaced_prefix reference continuation depth j (Finset.mem_range.mp hj))
  have shifted : addressShift depth (replacePairTail reference continuation depth)=continuation := by
    funext j
    simpa only [addressShift,Nat.add_zero] using
      congrFun (replaced_shift reference continuation depth 0) j
  change pairedAddress (replacePairTail reference continuation depth) ∈ affineFibre r level
  constructor
  · constructor <;> rw [← cantorSet_third_eq] <;> exact ⟨_,rfl⟩
  · have referenceEquation := referenceMember.2
    have continuationEquation := continuationMember.2
    change (r*address (1/3) (fun j => (reference j).1)+
      address (1/3) (fun j => (reference j).2))/2=level at referenceEquation
    have scaled := congrArg (fun value : ℝ => (1/3 : ℝ)^depth*value) continuationEquation
    change (r*address (1/3) (fun j => (replacePairTail reference continuation depth j).1)+
      address (1/3) (fun j => (replacePairTail reference continuation depth j).2))/2=level
    rw [address_prefix_tail (by norm_num) (by norm_num)
      (fun j => (replacePairTail reference continuation depth j).1) depth,
      address_prefix_tail (by norm_num) (by norm_num)
      (fun j => (replacePairTail reference continuation depth j).2) depth,
      firstPrefix,secondPrefix]
    rw [address_prefix_tail (by norm_num) (by norm_num) (fun j => (reference j).1) depth,
      address_prefix_tail (by norm_num) (by norm_num) (fun j => (reference j).2) depth]
      at referenceEquation
    have firstShift : (fun j => (replacePairTail reference continuation depth (j+depth)).1)=
        (fun j => (continuation j).1) := congrArg (fun digits => fun j => (digits j).1) shifted
    have secondShift : (fun j => (replacePairTail reference continuation depth (j+depth)).2)=
        (fun j => (continuation j).2) := congrArg (fun digits => fun j => (digits j).2) shifted
    rw [firstShift,secondShift]
    change (1/3 : ℝ)^depth*((r*address (1/3) (fun j => (continuation j).1)+
      address (1/3) (fun j => (continuation j).2))/2) =
      (1/3 : ℝ)^depth*((r*address (1/3) (fun j => (reference (j+depth)).1)+
      address (1/3) (fun j => (reference (j+depth)).2))/2) at scaled
    nlinarith [scaled]

/-- Actual two incomparable strict return words in any uncountable affine
fibre. The words are represented by addresses and finite lengths. A differing
coordinate before both lengths proves incomparability without a coding axiom. -/
theorem uncountable_fibre_two_strict_returns (r level : ℝ) (positive : 1 < r)
    (uncountable : ¬ (affineFibre r level).Countable) :
    ∃ left ∈ affineAddressFibre r level, ∃ right ∈ affineAddressFibre r level,
      ∃ leftLength rightLength difference : ℕ,
        difference < leftLength ∧ difference < rightLength ∧
        left difference ≠ right difference ∧
        normalizedAffineLevel r left leftLength ∈ strictSwitchSet r ∧
        normalizedAffineLevel r right rightLength ∈ strictSwitchSet r := by
  obtain ⟨left,leftMember,right,rightMember,depth,agreement,different,
    leftUncountable,rightUncountable⟩ := uncountable_addresses_branch
      (affineAddressFibre r level) (affineAddressFibre_uncountable r level uncountable)
  obtain ⟨leftContinuation,leftContinuationMember,leftDepth,leftStrict⟩ :=
    uncountable_fibre_strict_descendant r (normalizedAffineLevel r left (depth+1)) positive
      (uncountable_normalized_fibre r level left leftMember (depth+1) leftUncountable)
  obtain ⟨rightContinuation,rightContinuationMember,rightDepth,rightStrict⟩ :=
    uncountable_fibre_strict_descendant r (normalizedAffineLevel r right (depth+1)) positive
      (uncountable_normalized_fibre r level right rightMember (depth+1) rightUncountable)
  refine ⟨replacePairTail left leftContinuation (depth+1),
    replacement_in_fibre r level left leftContinuation leftMember (depth+1) leftContinuationMember,
    replacePairTail right rightContinuation (depth+1),
    replacement_in_fibre r level right rightContinuation rightMember (depth+1) rightContinuationMember,
    depth+1+leftDepth,depth+1+rightDepth,depth,by omega,by omega, ?_, ?_, ?_⟩
  · simpa [replacePairTail] using different
  · unfold normalizedAffineLevel
    rw [replaced_shift]
    exact leftStrict
  · unfold normalizedAffineLevel
    rw [replaced_shift]
    exact rightStrict

theorem irrational_switch_two_strict_returns (r level : ℝ) (good : GoodSlope r)
    (irrational : ∀ q : ℚ, r ≠ (q : ℝ)) (switch : level ∈ switchSet r) :
    ∃ left ∈ affineAddressFibre r level, ∃ right ∈ affineAddressFibre r level,
      ∃ leftLength rightLength difference : ℕ,
        difference < leftLength ∧ difference < rightLength ∧
        left difference ≠ right difference ∧
        normalizedAffineLevel r left leftLength ∈ strictSwitchSet r ∧
        normalizedAffineLevel r right rightLength ∈ strictSwitchSet r :=
  uncountable_fibre_two_strict_returns r level (goodSlope_between_one_three good).1
    (irrational_good_switch_uncountable r level good irrational switch)

end LambdaCantor.Integer
