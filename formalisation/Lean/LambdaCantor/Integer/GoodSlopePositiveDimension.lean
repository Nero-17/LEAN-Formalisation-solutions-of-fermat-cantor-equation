import LambdaCantor.Integer.GoodSlopeReturnAdapter
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Perfect

noncomputable section
open scoped NNReal Topology
namespace LambdaCantor.Integer
open Last

theorem pairedAddress_prefix_separation (depth : ℕ) (first second : ℕ → Bool × Bool)
    (different : ∃ index < depth, first index ≠ second index) :
    (1/3 : ℝ)^(depth+1) ≤ dist (pairedAddress first) (pairedAddress second) := by
  induction depth generalizing first second with
  | zero => obtain ⟨index,impossible,_⟩ := different; omega
  | succ depth inductionHypothesis =>
      by_cases head_eq : first 0 = second 0
      · have tails_differ : ∃ index < depth, first (index+1) ≠ second (index+1) := by
          obtain ⟨index,before,unequal⟩ := different
          cases index with
          | zero => exact False.elim (unequal head_eq)
          | succ index => exact ⟨index,by omega,unequal⟩
        have bound := inductionHypothesis (fun index => first (index+1)) (fun index => second (index+1)) tails_differ
        have first_step := paired_prefix_decomposition first 1
        have second_step := paired_prefix_decomposition second 1
        simp only [pairedPrefix,List.ofFn_succ,List.ofFn_zero,Fin.val_zero,addressShift] at first_step second_step
        rw [first_step,second_step,head_eq,wordMap_distance]
        norm_num only [List.length_singleton,pow_one,abs_of_pos (by norm_num : (0:ℝ)<1/3)]
        rw [pow_succ]
        have first_tail : addressShift 1 first = (fun index => first (index+1)) := by
          funext index
          simp only [addressShift]
        have second_tail : addressShift 1 second = (fun index => second (index+1)) := by
          funext index
          simp only [addressShift]
        rw [first_tail,second_tail]
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left bound (by norm_num : (0:ℝ)≤1/3)
      · have bound := first_digit_distance_gap (by norm_num : (0:ℝ)≤1/3) (by norm_num)
          (first 0) (second 0) head_eq
          (show pairedAddress (addressShift 1 first) ∈ cantorDust (1/3) from ⟨Set.mem_range_self _,Set.mem_range_self _⟩)
          (show pairedAddress (addressShift 1 second) ∈ cantorDust (1/3) from ⟨Set.mem_range_self _,Set.mem_range_self _⟩)
        have first_step := paired_prefix_decomposition first 1
        have second_step := paired_prefix_decomposition second 1
        simp only [pairedPrefix,List.ofFn_succ,List.ofFn_zero,Fin.val_zero] at first_step second_step
        rw [← first_step,← second_step] at bound
        have power_bound : (1/3 : ℝ)^(depth+1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        rw [pow_succ]
        nlinarith

/-- Non-isolation gives an actual second point in every metric ball; no
perfectness or uncountability assumption is inserted here. -/
theorem nonisolated_has_close_point {source : Set (ℝ × ℝ)} (point : source)
    (nonisolated : ¬ IsOpen ({point} : Set source)) (radius : ℝ) (positive : 0 < radius) :
    ∃ other : source, dist other.val point.val < radius ∧ other ≠ point := by
  classical
  by_contra absent
  push_neg at absent
  apply nonisolated
  apply Metric.isOpen_iff.mpr
  intro value member
  have equality : value = point := Set.mem_singleton_iff.mp member
  subst value
  refine ⟨radius,positive,?_⟩
  intro other close
  exact Set.mem_singleton_iff.mpr (absent other close)

/-- Equality of the source sets transports non-isolation together with the
point, including the membership proof in its subtype. -/
theorem nonisolated_source_eq {first second : Set (ℝ × ℝ)} (equality : first = second)
    (point : first) (nonisolated : ¬ IsOpen ({point} : Set first)) :
    ¬ IsOpen ({⟨point.val,equality ▸ point.property⟩} : Set second) := by
  subst second
  exact nonisolated

/-- At any prescribed minimum depth, a nonisolated fibre point has two
distinct immediate child cylinders on its actual defining level. -/
theorem nonisolated_deep_branching (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (point : {point : ℝ × ℝ | point ∈ cantorDust (1/3) ∧ function point = level})
    (nonisolated : ¬ IsOpen ({point} : Set {point : ℝ × ℝ | point ∈ cantorDust (1/3) ∧ function point = level}))
    (minimumDepth : ℕ) :
    ∃ word : List (Bool × Bool), minimumDepth ≤ word.length ∧ point.val ∈ wordCylinder (1/3) word ∧
      ∃ firstDigit secondDigit : Bool × Bool, firstDigit ≠ secondDigit ∧
      ∃ firstTail secondTail : ℝ × ℝ, firstTail ∈ cantorDust (1/3) ∧ secondTail ∈ cantorDust (1/3) ∧
      function (wordMap (1/3) word (wordMap (1/3) [firstDigit] firstTail)) = level ∧
      function (wordMap (1/3) word (wordMap (1/3) [secondDigit] secondTail)) = level := by
  classical
  obtain ⟨firstX,firstX_eq⟩ := point.property.1.1
  obtain ⟨firstY,firstY_eq⟩ := point.property.1.2
  let first : ℕ → Bool × Bool := fun index => (firstX index,firstY index)
  have first_eq : pairedAddress first = point.val := Prod.ext firstX_eq firstY_eq
  obtain ⟨other,close,different⟩ := nonisolated_has_close_point point nonisolated
    ((1/3 : ℝ)^(minimumDepth+1)) (by positivity)
  obtain ⟨secondX,secondX_eq⟩ := other.property.1.1
  obtain ⟨secondY,secondY_eq⟩ := other.property.1.2
  let second : ℕ → Bool × Bool := fun index => (secondX index,secondY index)
  have second_eq : pairedAddress second = other.val := Prod.ext secondX_eq secondY_eq
  have exists_difference : ∃ index, first index ≠ second index := by
    by_contra absent
    push_neg at absent
    have equal_digits : first = second := funext absent
    apply different
    apply Subtype.ext
    rw [← second_eq,← first_eq,equal_digits]
  let depth := Nat.find exists_difference
  have unequal : first depth ≠ second depth := Nat.find_spec exists_difference
  have agreement : ∀ index < depth, first index = second index := by
    intro index before
    exact not_not.mp (Nat.find_min exists_difference before)
  have deep : minimumDepth ≤ depth := by
    by_contra contrary
    have separated := pairedAddress_prefix_separation minimumDepth first second ⟨depth,by omega,unequal⟩
    rw [first_eq,second_eq,dist_comm] at separated
    exact (not_lt_of_ge separated) close
  have prefixes_eq : pairedPrefix first depth = pairedPrefix second depth := by
    unfold pairedPrefix
    congr 1
    funext index
    exact agreement index index.isLt
  have first_decomposition := paired_prefix_decomposition first depth
  have second_decomposition := paired_prefix_decomposition second depth
  have first_step := paired_prefix_decomposition (addressShift depth first) 1
  have second_step := paired_prefix_decomposition (addressShift depth second) 1
  simp only [pairedPrefix,List.ofFn_succ,List.ofFn_zero,Fin.val_zero,addressShift,Nat.zero_add] at first_step second_step
  refine ⟨pairedPrefix first depth,by simpa using deep,?_,first depth,second depth,unequal,
    pairedAddress (addressShift 1 (addressShift depth first)),
    pairedAddress (addressShift 1 (addressShift depth second)),
    ⟨Set.mem_range_self _,Set.mem_range_self _⟩,⟨Set.mem_range_self _,Set.mem_range_self _⟩,?_,?_⟩
  · exact ⟨pairedAddress (addressShift depth first),⟨Set.mem_range_self _,Set.mem_range_self _⟩,
      first_decomposition.symm.trans first_eq⟩
  · rw [← first_step,← first_decomposition,first_eq]
    exact point.property.2
  · rw [prefixes_eq,← second_step,← second_decomposition,second_eq]
    exact other.property.2

theorem goodSlopeLinear_dust_bounds (slope : ℝ) (positive : 0 ≤ slope)
    {point : ℝ × ℝ} (membership : point ∈ cantorDust (1/3)) :
    0 ≤ goodSlopeLinear slope point ∧ goodSlopeLinear slope point ≤ (slope+1)/2 := by
  have first := cantorSet_subset_unitInterval (by norm_num) (by norm_num) membership.1
  have second := cantorSet_subset_unitInterval (by norm_num) (by norm_num) membership.2
  rw [goodSlopeLinear_apply]
  constructor <;> nlinarith [first.1,first.2,second.1,second.2,mul_nonneg positive first.1,
    mul_le_mul_of_nonneg_left first.2 positive]

theorem goodSlopeLinear_child (slope : ℝ) (digit : Bool × Bool) (point : ℝ × ℝ) :
    goodSlopeLinear slope (wordMap (1/3) [digit] point) =
      childOffset slope (digitPairLabel digit)/3 + goodSlopeLinear slope point/3 := by
  rcases digit with ⟨first,second⟩
  cases first <;> cases second <;>
    simp [goodSlopeLinear_apply,wordMap,digitPoint,childOffset,digitPairLabel] <;> ring

/-- The true function level in a retained cylinder differs from its affine
child level by at most the Lipschitz error constant, uniformly in its depth. -/
theorem retained_child_approximate_image (slope : ℝ) (positive : 0 ≤ slope)
    (function : (ℝ × ℝ) → ℝ) (level : ℝ) (word : List (Bool × Bool)) (bound : ℝ≥0)
    (small_error : LipschitzOnWith bound (fun value => function value-goodSlopeLinear slope value)
      (wordCylinder (1/3) word))
    (digit : Bool × Bool) (tail : ℝ × ℝ) (tail_mem : tail ∈ cantorDust (1/3))
    (equation : function (wordMap (1/3) word (wordMap (1/3) [digit] tail)) = level) :
    approximateChildImage slope ((level-function (wordMap (1/3) word 0))/(1/3 : ℝ)^word.length)
      bound (digitPairLabel digit) := by
  let child := wordMap (1/3) [digit] tail
  have child_mem : child ∈ cantorDust (1/3) := wordMap_mem_dust (by norm_num) (by norm_num) [digit] tail_mem
  have corner_mem : (0 : ℝ × ℝ) ∈ cantorDust (1/3) := ⟨zero_mem_cantorSet _,zero_mem_cantorSet _⟩
  have error_bound := small_error.dist_le_mul
    (wordMap (1/3) word child)
    (show wordMap (1/3) word child ∈ wordCylinder (1/3) word from ⟨child,child_mem,rfl⟩)
    (wordMap (1/3) word 0)
    (show wordMap (1/3) word 0 ∈ wordCylinder (1/3) word from ⟨0,corner_mem,rfl⟩)
  rw [Real.dist_eq,wordMap_distance,abs_of_pos (by norm_num : (0:ℝ)<1/3)] at error_bound
  have distance_bound := dust_dist_le_one (by norm_num : (0:ℝ)≤1/3) (by norm_num) child_mem corner_mem
  have bound_scaled : |(function (wordMap (1/3) word child)-goodSlopeLinear slope (wordMap (1/3) word child)) -
      (function (wordMap (1/3) word 0)-goodSlopeLinear slope (wordMap (1/3) word 0))| ≤
      (bound : ℝ)*(1/3 : ℝ)^word.length := error_bound.trans (by
        calc
          (bound : ℝ)*((1/3 : ℝ)^word.length*dist child 0) =
              ((bound : ℝ)*(1/3 : ℝ)^word.length)*dist child 0 := (mul_assoc _ _ _).symm
          _ ≤ ((bound : ℝ)*(1/3 : ℝ)^word.length)*1 :=
            mul_le_mul_of_nonneg_left distance_bound
              (mul_nonneg bound.coe_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤1/3) word.length))
          _ = (bound : ℝ)*(1/3 : ℝ)^word.length := mul_one _)
  have linear_identity : goodSlopeLinear slope (wordMap (1/3) word child) =
      goodSlopeLinear slope (wordMap (1/3) word 0) + (1/3 : ℝ)^word.length*goodSlopeLinear slope child := by
    rw [wordMap_affine,map_add,map_smul]
    rfl
  rw [equation,linear_identity] at bound_scaled
  have normalized_bound : |(level-function (wordMap (1/3) word 0))/(1/3 : ℝ)^word.length -
      goodSlopeLinear slope child| ≤ (bound : ℝ) := by
    have quotient_identity : (level-function (wordMap (1/3) word 0))/(1/3 : ℝ)^word.length -
        goodSlopeLinear slope child = (level-function (wordMap (1/3) word 0) -
          (1/3 : ℝ)^word.length*goodSlopeLinear slope child)/(1/3 : ℝ)^word.length := by
      field_simp
      <;> ring
    rw [quotient_identity]
    rw [abs_div,abs_of_pos (pow_pos (by norm_num : (0:ℝ)<1/3) _)]
    apply (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<1/3) _)).mpr
    convert bound_scaled using 1 <;> congr 1 <;> ring
  have sides := abs_le.mp normalized_bound
  have tail_bounds := goodSlopeLinear_dust_bounds slope positive tail_mem
  have child_linear := goodSlopeLinear_child slope digit tail
  change goodSlopeLinear slope child = _ at child_linear
  unfold approximateChildImage
  constructor <;> linarith [sides.1,sides.2,tail_bounds.1,tail_bounds.2]

/-- An actual strictly differentiable Cantor level has positive dimension at
every nonisolated point with a normalized irrational certified tangent. The
deep branching cylinder is constructed above, rather than assumed. -/
theorem good_slope_positive_dimension (slope : ℝ) (good : GoodSlope slope)
    (irrational : ∀ rational : ℚ, slope ≠ (rational : ℝ))
    (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (point : {point : ℝ × ℝ | point ∈ cantorDust (1/3) ∧ function point = level})
    (nonisolated : ¬ IsOpen ({point} : Set {point : ℝ × ℝ | point ∈ cantorDust (1/3) ∧ function point = level}))
    (derivative : HasStrictFDerivAt function (goodSlopeLinear slope) point.val) :
    0 < dimH {point : ℝ × ℝ | point ∈ cantorDust (1/3) ∧ function point = level} := by
  obtain ⟨threshold,threshold_positive,neighborhood,neighborhood_open,contained,criterion⟩ :=
    good_slope_local_source_criterion slope good irrational
  have compact : IsCompact (switchSet slope) := (isCompact_Icc.union isCompact_Icc).union isCompact_Icc
  obtain ⟨radius,radius_positive,thickening⟩ := compact.exists_cthickening_subset_open neighborhood_open contained
  have slope_bounds := goodSlope_between_one_three good
  have slope_gap_positive : 0 < slope-1 := by linarith [slope_bounds.1]
  let bound : ℝ≥0 := ⟨min (threshold/2) (min (radius/2) ((slope-1)/24)), by positivity⟩
  have bound_positive : 0 < bound := by
    change 0 < min (threshold/2) (min (radius/2) ((slope-1)/24))
    exact lt_min (by positivity) (lt_min (by positivity) (by linarith [slope_bounds.1]))
  have bound_threshold : (bound : ℝ) < threshold := by
    have := min_le_left (threshold/2) (min (radius/2) ((slope-1)/24))
    change min (threshold/2) (min (radius/2) ((slope-1)/24)) < threshold
    linarith
  have bound_radius : (bound : ℝ) ≤ radius := by
    have first := min_le_right (threshold/2) (min (radius/2) ((slope-1)/24))
    have second := min_le_left (radius/2) ((slope-1)/24)
    change min (threshold/2) (min (radius/2) ((slope-1)/24)) ≤ radius
    linarith
  have bound_gap : 2*(bound : ℝ) < (slope-1)/6 := by
    have first := min_le_right (threshold/2) (min (radius/2) ((slope-1)/24))
    have second := min_le_right (radius/2) ((slope-1)/24)
    change 2*min (threshold/2) (min (radius/2) ((slope-1)/24)) < (slope-1)/6
    linarith [slope_bounds.1]
  obtain ⟨minimumDepth,small_error⟩ := strict_derivative_cylinder_error
    (by norm_num : (0:ℝ)<1/3) (by norm_num) derivative bound bound_positive
  obtain ⟨word,deep,point_mem,firstDigit,secondDigit,different,firstTail,secondTail,
    first_mem,second_mem,first_equation,second_equation⟩ := nonisolated_deep_branching function level point nonisolated minimumDepth
  have error := small_error word deep point_mem
  have first_image := retained_child_approximate_image slope (by linarith [slope_bounds.1])
    function level word bound error firstDigit firstTail first_mem first_equation
  have second_image := retained_child_approximate_image slope (by linarith [slope_bounds.1])
    function level word bound error secondDigit secondTail second_mem second_equation
  have expanded := branching_in_expanded_switch slope _ (bound : ℝ) slope_bounds.1 bound_gap
    (digitPairLabel firstDigit) (digitPairLabel secondDigit)
    (fun equality => different (digitPairLabel_injective equality)) first_image second_image
  obtain ⟨base,base_mem,distance⟩ := expanded_switch_close slope _ (bound : ℝ)
    slope_bounds.1.le slope_bounds.2.le bound.coe_nonneg expanded
  apply criterion bound bound_threshold function level word error
  apply thickening
  exact Metric.mem_cthickening_of_dist_le _ base radius (switchSet slope) base_mem
    (by simpa only [Real.dist_eq] using distance.trans bound_radius)

/-- Scale an actual derivative with positive vertical component to the
normalized tangent used by the return theorem. The level set is unchanged. -/
theorem good_slope_positive_dimension_of_derivative
    (function : (ℝ × ℝ) → ℝ) (level horizontal vertical : ℝ) (vertical_positive : 0 < vertical)
    (good : GoodSlope (horizontal/vertical))
    (irrational : ∀ rational : ℚ, horizontal/vertical ≠ (rational : ℝ))
    (point : {point : ℝ × ℝ | point ∈ cantorDust (1/3) ∧ function point = level})
    (nonisolated : ¬ IsOpen ({point} : Set {point : ℝ × ℝ | point ∈ cantorDust (1/3) ∧ function point = level}))
    (derivative : (ℝ × ℝ) →L[ℝ] ℝ) (strict : HasStrictFDerivAt function derivative point.val)
    (formula : ∀ direction, derivative direction = horizontal*direction.1+vertical*direction.2) :
    0 < dimH {point : ℝ × ℝ | point ∈ cantorDust (1/3) ∧ function point = level} := by
  have scale_nonzero : (1/(2*vertical) : ℝ) ≠ 0 := by positivity
  let normalized : (ℝ × ℝ) → ℝ := fun value => (1/(2*vertical))*function value
  have source_eq : {value : ℝ × ℝ | value ∈ cantorDust (1/3) ∧ normalized value = (1/(2*vertical))*level} =
      {value : ℝ × ℝ | value ∈ cantorDust (1/3) ∧ function value = level} := by
    ext value
    constructor
    · rintro ⟨membership,equality⟩
      exact ⟨membership,mul_left_cancel₀ scale_nonzero equality⟩
    · rintro ⟨membership,equality⟩
      exact ⟨membership,congrArg (fun real : ℝ => (1/(2*vertical))*real) equality⟩
  have linear_eq : (1/(2*vertical)) • derivative = goodSlopeLinear (horizontal/vertical) := by
    apply ContinuousLinearMap.ext
    intro direction
    change (1/(2*vertical))*derivative direction = goodSlopeLinear (horizontal/vertical) direction
    rw [formula,goodSlopeLinear_apply]
    field_simp [ne_of_gt vertical_positive]
    <;> ring
  have normalized_strict := strict.const_smul (1/(2*vertical))
  rw [linear_eq] at normalized_strict
  have dimension := good_slope_positive_dimension (horizontal/vertical) good irrational normalized
    ((1/(2*vertical))*level) ⟨point.val,by rw [source_eq]; exact point.property⟩
    (nonisolated_source_eq source_eq.symm point nonisolated) normalized_strict
  rwa [source_eq] at dimension

/-- A perfect subset of the level suffices: the full level need not itself be
perfect. This is the perfect-subset formulation of the manuscript's irrational
tangent lemma; its local C1 hypothesis supplies the strict derivative used by
the robust return construction. -/
theorem good_slope_positive_dimension_of_perfect_subset
    (function : (ℝ × ℝ) → ℝ) (level horizontal vertical : ℝ)
    (vertical_positive : 0 < vertical)
    (good : GoodSlope (horizontal/vertical))
    (irrational : ∀ rational : ℚ, horizontal/vertical ≠ (rational : ℝ))
    (source : Set (ℝ × ℝ)) (perfect : Perfect source)
    (contained : source ⊆ {point : ℝ × ℝ | point ∈ cantorDust (1/3) ∧ function point = level})
    (point : ℝ × ℝ) (membership : point ∈ source)
    (smooth : ContDiffAt ℝ 1 function point)
    (derivative : (ℝ × ℝ) →L[ℝ] ℝ) (differentiable : HasFDerivAt function derivative point)
    (formula : ∀ direction, derivative direction = horizontal*direction.1+vertical*direction.2) :
    0 < dimH {point : ℝ × ℝ | point ∈ cantorDust (1/3) ∧ function point = level} := by
  apply good_slope_positive_dimension_of_derivative function level horizontal vertical
    vertical_positive good irrational ⟨point,contained membership⟩ _ derivative
    (smooth.hasStrictFDerivAt' differentiable (by norm_num)) formula
  intro isolated
  obtain ⟨radius,positive,ball⟩ := Metric.isOpen_iff.mp isolated
    (⟨point,contained membership⟩ : {point : ℝ × ℝ | point ∈ cantorDust (1/3) ∧ function point = level})
    (by simp)
  obtain ⟨other,⟨nearby,other_member⟩,different⟩ :=
    (preperfect_iff_nhds.mp perfect.2) point membership (Metric.ball point radius)
      (Metric.ball_mem_nhds point positive)
  apply different
  have equality : (⟨other,contained other_member⟩ :
      {point : ℝ × ℝ | point ∈ cantorDust (1/3) ∧ function point = level}) =
        ⟨point,contained membership⟩ := Set.mem_singleton_iff.mp (ball nearby)
  exact congrArg Subtype.val equality

end LambdaCantor.Integer
