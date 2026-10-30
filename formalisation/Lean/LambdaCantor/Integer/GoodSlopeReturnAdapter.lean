import LambdaCantor.Integer.AffineUniformReturns
import LambdaCantor.Last.LocalSource
import Mathlib.Data.List.OfFn

noncomputable section
open scoped NNReal Topology
namespace LambdaCantor.Integer
open Last

def pairedPrefix (digits : ℕ → Bool × Bool) (depth : ℕ) : List (Bool × Bool) :=
  List.ofFn (fun index : Fin depth => digits index)

@[simp] theorem pairedPrefix_length (digits : ℕ → Bool × Bool) (depth : ℕ) :
    (pairedPrefix digits depth).length = depth := by simp [pairedPrefix]

theorem paired_prefix_decomposition (digits : ℕ → Bool × Bool) (depth : ℕ) :
    pairedAddress digits = wordMap (1/3) (pairedPrefix digits depth)
      (pairedAddress (addressShift depth digits)) := by
  induction depth generalizing digits with
  | zero =>
      have shift_zero : addressShift 0 digits = digits := by
        funext index
        simp only [addressShift,Nat.add_zero]
      simpa only [pairedPrefix,List.ofFn_zero,wordMap_nil] using
        congrArg pairedAddress shift_zero.symm
  | succ depth inductionHypothesis =>
      have head : pairedAddress digits = wordMap (1/3) [digits 0]
          (pairedAddress (fun index => digits (index+1))) := by
        apply Prod.ext
        · exact address_first_digit (by norm_num) (by norm_num) _
        · exact address_first_digit (by norm_num) (by norm_num) _
      have prefix_step : pairedPrefix digits (depth+1) =
          digits 0 :: pairedPrefix (fun index => digits (index+1)) depth := by
        simpa only [pairedPrefix,Fin.val_zero,Fin.val_succ] using
          (List.ofFn_succ (f := fun index : Fin (depth+1) => digits index))
      have shift_step : addressShift depth (fun index => digits (index+1)) =
          addressShift (depth+1) digits := by
        funext index
        change digits (index+depth+1) = digits (index+(depth+1))
        exact congrArg digits (Nat.add_assoc index depth 1)
      rw [head,prefix_step]
      change wordMap (1/3) [digits 0] (pairedAddress (fun index => digits (index+1))) =
        wordMap (1/3) [digits 0] (wordMap (1/3)
          (pairedPrefix (fun index => digits (index+1)) depth)
          (pairedAddress (addressShift (depth+1) digits)))
      rw [← shift_step]
      exact congrArg (wordMap (1/3) [digits 0])
        (inductionHypothesis (fun index => digits (index+1)))

theorem paired_prefix_corner (digits : ℕ → Bool × Bool) (depth : ℕ) :
    wordMap (1/3) (pairedPrefix digits depth) 0 =
      (prefixValue (1/3) (fun index => (digits index).1) depth,
        prefixValue (1/3) (fun index => (digits index).2) depth) := by
  have decomposition := paired_prefix_decomposition digits depth
  rw [wordMap_affine, pairedPrefix_length] at decomposition
  have first := congrArg Prod.fst decomposition
  have second := congrArg Prod.snd decomposition
  have first_address := address_prefix_tail (by norm_num : (0 : ℝ) ≤ 1/3)
    (by norm_num : (1/3 : ℝ) < 1) (fun index => (digits index).1) depth
  have second_address := address_prefix_tail (by norm_num : (0 : ℝ) ≤ 1/3)
    (by norm_num : (1/3 : ℝ) < 1) (fun index => (digits index).2) depth
  dsimp [pairedAddress, addressShift] at first second
  apply Prod.ext <;> linarith

def goodSlopeLinear (slope : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (slope/2) • ContinuousLinearMap.fst ℝ ℝ ℝ + (1/2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem goodSlopeLinear_apply (slope : ℝ) (point : ℝ × ℝ) :
    goodSlopeLinear slope point = (slope*point.1+point.2)/2 := by
  simp [goodSlopeLinear]
  <;> ring

theorem paired_prefix_return (slope level : ℝ) (digits : ℕ → Bool × Bool) (depth : ℕ) :
    linearWordReturn (1/3) (goodSlopeLinear slope).toLinearMap (pairedPrefix digits depth) level =
      affineWordLevel slope digits depth level := by
  unfold linearWordReturn returnLevel affineWordLevel
  rw [pairedPrefix_length, paired_prefix_corner]
  change (level-goodSlopeLinear slope
    (prefixValue (1/3) (fun index => (digits index).1) depth,
      prefixValue (1/3) (fun index => (digits index).2) depth))/(1/3 : ℝ)^depth = _
  rw [goodSlopeLinear_apply]

theorem words_diverge_of_difference (first second : List (Bool × Bool))
    (different : ∃ index, ∃ first_bound : index < first.length, ∃ second_bound : index < second.length,
      first[index] ≠ second[index]) : WordsDiverge first second := by
  induction first generalizing second with
  | nil => obtain ⟨index, impossible, _⟩ := different; simp at impossible
  | cons firstDigit rest inductionHypothesis =>
      cases second with
      | nil => obtain ⟨index, _, impossible, _⟩ := different; simp at impossible
      | cons secondDigit secondRest =>
          by_cases equal : firstDigit = secondDigit
          · subst secondDigit
            obtain ⟨index, first_bound, second_bound, unequal⟩ := different
            cases index with
            | zero => simp at unequal
            | succ index =>
                obtain ⟨common,left,right,leftRest,rightRest,different,left_eq,right_eq⟩ :=
                  inductionHypothesis secondRest ⟨index,by simpa using first_bound,
                    by simpa using second_bound,by simpa using unequal⟩
                exact ⟨firstDigit::common,left,right,leftRest,rightRest,different,
                  by simp [left_eq],by simp [right_eq]⟩
          · exact ⟨[],firstDigit,secondDigit,rest,secondRest,equal,rfl,rfl⟩

def AffineReturnPair.toReturnPair {slope : ℝ} (pair : AffineReturnPair slope) : ReturnPair where
  word bit := if bit then pairedPrefix pair.right pair.rightLength else pairedPrefix pair.left pair.leftLength
  length_pos := by
    have left := pair.beforeLeft
    have right := pair.beforeRight
    intro bit
    cases bit <;> simp only [Bool.false_eq_true,if_false,if_true,pairedPrefix_length] <;> omega
  diverge := by
    apply words_diverge_of_difference
    refine ⟨pair.difference,by simpa using pair.beforeLeft,by simpa using pair.beforeRight,?_⟩
    simpa [pairedPrefix] using pair.different

theorem good_slope_strict_return_pairs (slope : ℝ) (good : GoodSlope slope)
    (irrational : ∀ rational : ℚ, slope ≠ (rational : ℝ)) :
    ∀ level ∈ switchSet slope, ∃ pair : ReturnPair,
      linearWordReturn (1/3) (goodSlopeLinear slope).toLinearMap (pair.word false) level ∈ interior (switchSet slope) ∧
      linearWordReturn (1/3) (goodSlopeLinear slope).toLinearMap (pair.word true) level ∈ interior (switchSet slope) := by
  intro level membership
  obtain ⟨pair,positive⟩ := pointwise_strict_return_pair slope level good irrational membership
  have margins := lt_min_iff.mp positive
  have left := lt_min_iff.mp margins.1
  have right := lt_min_iff.mp margins.2
  refine ⟨pair.toReturnPair,?_,?_⟩
  · change linearWordReturn (1/3) (goodSlopeLinear slope).toLinearMap (pairedPrefix pair.left pair.leftLength) level ∈ _
    rw [paired_prefix_return]
    apply (interior_mono pair.leftTarget)
    rw [isOpen_Ioo.interior_eq]
    exact ⟨by linarith [left.1],by linarith [left.2]⟩
  · change linearWordReturn (1/3) (goodSlopeLinear slope).toLinearMap (pairedPrefix pair.right pair.rightLength) level ∈ _
    rw [paired_prefix_return]
    apply (interior_mono pair.rightTarget)
    rw [isOpen_Ioo.interior_eq]
    exact ⟨by linarith [right.1],by linarith [right.2]⟩

/-- The existing nonlinear local criterion now has actual strict-return data
for every irrational slope in the certified bands. The remaining theorem in
this module must construct its deep input cylinder from non-isolation. -/
theorem good_slope_local_source_criterion (slope : ℝ) (good : GoodSlope slope)
    (irrational : ∀ rational : ℚ, slope ≠ (rational : ℝ)) :
    ∃ threshold : ℝ, 0 < threshold ∧ ∃ neighborhood : Set ℝ,
      IsOpen neighborhood ∧ switchSet slope ⊆ neighborhood ∧
      ∀ bound : ℝ≥0, (bound : ℝ) < threshold →
      ∀ function : (ℝ × ℝ) → ℝ, ∀ level : ℝ, ∀ word : List (Bool × Bool),
      LipschitzOnWith bound (fun value => function value - goodSlopeLinear slope value) (wordCylinder (1/3) word) →
      (level-function (wordMap (1/3) word 0))/(1/3 : ℝ)^word.length ∈ neighborhood →
      0 < dimH {point : ℝ × ℝ | point ∈ cantorDust (1/3) ∧ function point = level} := by
  apply local_source_criterion (1/3) (by norm_num) (by norm_num) (goodSlopeLinear slope) (switchSet slope)
    ((isCompact_Icc.union isCompact_Icc).union isCompact_Icc)
  · have slope_bounds := goodSlope_between_one_three good
    exact ⟨1/3,Or.inl (Or.inl ⟨le_rfl,by linarith [slope_bounds.1]⟩)⟩
  · exact good_slope_strict_return_pairs slope good irrational

end LambdaCantor.Integer
