import LambdaCantor.Integer.AffineStrictReturns
import LambdaCantor.Integer.UniformReturns
import Mathlib.Topology.MetricSpace.Thickening

namespace LambdaCantor.Integer

noncomputable def affineWordLevel (r : ℝ) (digits : ℕ → Bool × Bool)
    (depth : ℕ) (level : ℝ) : ℝ :=
  (level-(r*prefixValue (1/3) (fun j => (digits j).1) depth+
    prefixValue (1/3) (fun j => (digits j).2) depth)/2)/(1/3 : ℝ)^depth

theorem affineWordLevel_eq_normalized (r level : ℝ) (digits : ℕ → Bool × Bool)
    (member : digits ∈ affineAddressFibre r level) (depth : ℕ) :
    affineWordLevel r digits depth level=normalizedAffineLevel r digits depth := by
  unfold affineWordLevel
  apply (div_eq_iff (by positivity : (1/3 : ℝ)^depth ≠ 0)).2
  have equation := member.2
  change (r*address (1/3) (fun j => (digits j).1)+
    address (1/3) (fun j => (digits j).2))/2=level at equation
  rw [address_prefix_tail (by norm_num) (by norm_num) (fun j => (digits j).1) depth,
    address_prefix_tail (by norm_num) (by norm_num) (fun j => (digits j).2) depth] at equation
  unfold normalizedAffineLevel pairedAddress addressShift
  dsimp only
  nlinarith [equation]

theorem affineWordLevel_continuous (r : ℝ) (digits : ℕ → Bool × Bool) (depth : ℕ) :
    Continuous (affineWordLevel r digits depth) :=
  (continuous_id.sub continuous_const).div_const _

private theorem strict_switch_interval (r u : ℝ) (strict : u ∈ strictSwitchSet r) :
    ∃ lower upper : ℝ, lower < u ∧ u < upper ∧ Set.Ioo lower upper ⊆ switchSet r := by
  rcases strict with (first | second) | third
  · refine ⟨1/3,(r+1)/6,first.1,first.2, ?_⟩
    intro v hv
    exact Or.inl (Or.inl ⟨hv.1.le,hv.2.le⟩)
  · refine ⟨r/3,(r+3)/6,second.1,second.2, ?_⟩
    intro v hv
    exact Or.inl (Or.inr ⟨hv.1.le,hv.2.le⟩)
  · refine ⟨(r+1)/3,(3*r+1)/6,third.1,third.2, ?_⟩
    intro v hv
    exact Or.inr ⟨hv.1.le,hv.2.le⟩

/-- A pair of finite prefix words together with two target intervals in the
switch set. The explicit differing index certifies incomparability. -/
structure AffineReturnPair (r : ℝ) where
  left : ℕ → Bool × Bool
  right : ℕ → Bool × Bool
  leftLength : ℕ
  rightLength : ℕ
  difference : ℕ
  beforeLeft : difference < leftLength
  beforeRight : difference < rightLength
  different : left difference ≠ right difference
  leftLower : ℝ
  leftUpper : ℝ
  rightLower : ℝ
  rightUpper : ℝ
  leftTarget : Set.Ioo leftLower leftUpper ⊆ switchSet r
  rightTarget : Set.Ioo rightLower rightUpper ⊆ switchSet r

noncomputable def AffineReturnPair.gap {r : ℝ} (pair : AffineReturnPair r) (level : ℝ) : ℝ :=
  min (min (affineWordLevel r pair.left pair.leftLength level-pair.leftLower)
    (pair.leftUpper-affineWordLevel r pair.left pair.leftLength level))
    (min (affineWordLevel r pair.right pair.rightLength level-pair.rightLower)
    (pair.rightUpper-affineWordLevel r pair.right pair.rightLength level))

theorem AffineReturnPair.continuous_gap {r : ℝ} (pair : AffineReturnPair r) :
    Continuous pair.gap := by
  unfold AffineReturnPair.gap
  exact (((affineWordLevel_continuous _ _ _).sub continuous_const).min
    (continuous_const.sub (affineWordLevel_continuous _ _ _))).min
    (((affineWordLevel_continuous _ _ _).sub continuous_const).min
      (continuous_const.sub (affineWordLevel_continuous _ _ _)))

theorem pointwise_strict_return_pair (r level : ℝ) (good : GoodSlope r)
    (irrational : ∀ q : ℚ, r ≠ (q : ℝ)) (switch : level ∈ switchSet r) :
    ∃ pair : AffineReturnPair r, 0 < pair.gap level := by
  obtain ⟨left,leftMember,right,rightMember,leftLength,rightLength,difference,
    beforeLeft,beforeRight,different,leftStrict,rightStrict⟩ :=
      irrational_switch_two_strict_returns r level good irrational switch
  obtain ⟨leftLower,leftUpper,leftLow,leftHigh,leftTarget⟩ :=
    strict_switch_interval r _ leftStrict
  obtain ⟨rightLower,rightUpper,rightLow,rightHigh,rightTarget⟩ :=
    strict_switch_interval r _ rightStrict
  refine ⟨⟨left,right,leftLength,rightLength,difference,beforeLeft,beforeRight,different,
    leftLower,leftUpper,rightLower,rightUpper,leftTarget,rightTarget⟩, ?_⟩
  unfold AffineReturnPair.gap
  dsimp only
  rw [affineWordLevel_eq_normalized r level left leftMember leftLength,
    affineWordLevel_eq_normalized r level right rightMember rightLength]
  exact lt_min (lt_min (sub_pos.mpr leftLow) (sub_pos.mpr leftHigh))
    (lt_min (sub_pos.mpr rightLow) (sub_pos.mpr rightHigh))

/-- Finite strict-return atlas with a common positive margin on all of B_r.
This is the complete affine compactness step; it does not yet assert robustness
under a nonlinear perturbation or a Hausdorff-dimension estimate. -/
theorem finite_uniform_affine_returns (r : ℝ) (good : GoodSlope r)
    (irrational : ∀ q : ℚ, r ≠ (q : ℝ)) :
    ∃ selected : Finset (AffineReturnPair r), ∃ margin > 0,
      ∀ level ∈ switchSet r, ∃ pair ∈ selected, margin < pair.gap level := by
  apply compact_uniform_strict_margin (switchSet r)
    ((isCompact_Icc.union isCompact_Icc).union isCompact_Icc)
    (fun pair : AffineReturnPair r => pair.gap) (fun pair => pair.continuous_gap)
  intro level switch
  exact pointwise_strict_return_pair r level good irrational switch

theorem bounded_uniform_affine_returns (r : ℝ) (good : GoodSlope r)
    (irrational : ∀ q : ℚ, r ≠ (q : ℝ)) :
    ∃ bound : ℕ, 0 < bound ∧ ∃ selected : Finset (AffineReturnPair r),
      (∀ pair ∈ selected, pair.leftLength ≤ bound ∧ pair.rightLength ≤ bound) ∧
      ∃ margin > 0, ∀ level ∈ switchSet r,
        ∃ pair ∈ selected, margin < pair.gap level := by
  obtain ⟨selected,margin,positive,cover⟩ := finite_uniform_affine_returns r good irrational
  refine ⟨1+selected.sup (fun pair => max pair.leftLength pair.rightLength),
    by omega,selected, ?_,margin,positive,cover⟩
  intro pair member
  have upper := Finset.le_sup (f := fun pair : AffineReturnPair r =>
    max pair.leftLength pair.rightLength) member
  constructor
  · have left := le_max_left pair.leftLength pair.rightLength
    omega
  · have right := le_max_right pair.leftLength pair.rightLength
    omega

/-- The same finite return atlas works on a whole neighborhood of B_r. This
is the entry-level neighborhood needed for deep branching cylinders of a C1
curve; robustness of the descendants is a separate strict-return theorem. -/
theorem neighborhood_uniform_affine_returns (r : ℝ) (good : GoodSlope r)
    (irrational : ∀ q : ℚ, r ≠ (q : ℝ)) :
    ∃ selected : Finset (AffineReturnPair r), ∃ margin > 0, ∃ radius > 0,
      ∀ level, (∃ base ∈ switchSet r, |level-base| ≤ radius) →
        ∃ pair ∈ selected, margin < pair.gap level := by
  classical
  obtain ⟨selected,margin,positive,cover⟩ := finite_uniform_affine_returns r good irrational
  have compact : IsCompact (switchSet r) :=
    (isCompact_Icc.union isCompact_Icc).union isCompact_Icc
  have openCover : IsOpen (⋃ pair ∈ selected, {level : ℝ | margin < pair.gap level}) :=
    isOpen_biUnion (fun pair _ => isOpen_lt continuous_const pair.continuous_gap)
  have contained : switchSet r ⊆ ⋃ pair ∈ selected, {level : ℝ | margin < pair.gap level} := by
    intro level member
    obtain ⟨pair,pair_member,bound⟩ := cover level member
    exact Set.mem_iUnion.mpr ⟨pair,Set.mem_iUnion.mpr ⟨pair_member,bound⟩⟩
  obtain ⟨radius,radiusPositive,neighborhood⟩ := compact.exists_cthickening_subset_open
    openCover contained
  refine ⟨selected,margin,positive,radius,radiusPositive, ?_⟩
  intro level close
  obtain ⟨base,baseMember,distance⟩ := close
  have member := Metric.mem_cthickening_of_dist_le level base radius (switchSet r)
    baseMember (by simpa only [Real.dist_eq] using distance)
  obtain ⟨pair,pair_member⟩ := Set.mem_iUnion.mp (neighborhood member)
  obtain ⟨selected_member,bound⟩ := Set.mem_iUnion.mp pair_member
  exact ⟨pair,selected_member,bound⟩

end LambdaCantor.Integer
