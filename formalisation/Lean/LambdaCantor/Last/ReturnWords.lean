import LambdaCantor.SelfSimilarity
import LambdaCantor.Last.StrictReturns
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

noncomputable section
namespace LambdaCantor.Last

def digitPoint (digit : Bool × Bool) : ℝ × ℝ :=
  (if digit.1 then 1 else 0, if digit.2 then 1 else 0)

/-- The actual Cantor similitude belonging to a finite paired word. -/
def wordMap (ratio : ℝ) : List (Bool × Bool) → (ℝ × ℝ) → (ℝ × ℝ)
  | [], point => point
  | digit :: rest, point => (1 - ratio) • digitPoint digit + ratio • wordMap ratio rest point

@[simp] theorem wordMap_nil (ratio : ℝ) (point : ℝ × ℝ) :
    wordMap ratio [] point = point := rfl

theorem wordMap_append (ratio : ℝ) (first second : List (Bool × Bool))
    (point : ℝ × ℝ) :
    wordMap ratio (first ++ second) point = wordMap ratio first (wordMap ratio second point) := by
  induction first with
  | nil => rfl
  | cons digit rest ih => simp only [List.cons_append, wordMap, ih]

theorem wordMap_affine (ratio : ℝ) (word : List (Bool × Bool)) (point : ℝ × ℝ) :
    wordMap ratio word point = wordMap ratio word 0 + ratio ^ word.length • point := by
  induction word with
  | nil => simp [wordMap]
  | cons digit rest ih =>
    simp only [wordMap, List.length_cons, ih, smul_add, smul_smul, pow_succ]
    rw [mul_comm (ratio ^ rest.length) ratio, add_assoc]

theorem wordMap_distance (ratio : ℝ) (word : List (Bool × Bool))
    (first second : ℝ × ℝ) :
    dist (wordMap ratio word first) (wordMap ratio word second) =
      |ratio| ^ word.length * dist first second := by
  rw [wordMap_affine ratio word first, wordMap_affine ratio word second,
    dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_pow]

theorem continuous_wordMap (ratio : ℝ) (word : List (Bool × Bool)) :
    Continuous (wordMap ratio word) := by
  have heq : wordMap ratio word = fun point => wordMap ratio word 0 + ratio ^ word.length • point :=
    funext (wordMap_affine ratio word)
  rw [heq]
  have hscale : Continuous (fun point : ℝ × ℝ => ratio ^ word.length • point) :=
    continuous_id.const_smul (ratio ^ word.length)
  exact continuous_const.add hscale

def cantorDust (ratio : ℝ) : Set (ℝ × ℝ) := cantorSet ratio ×ˢ cantorSet ratio

theorem wordMap_mem_dust {ratio : ℝ} (hnonnegative : 0 ≤ ratio) (hless : ratio < 1)
    (word : List (Bool × Bool)) {point : ℝ × ℝ} (hpoint : point ∈ cantorDust ratio) :
    wordMap ratio word point ∈ cantorDust ratio := by
  induction word with
  | nil => exact hpoint
  | cons digit rest ih =>
    change ((1 - ratio) * (if digit.1 then 1 else 0) + ratio * (wordMap ratio rest point).1 ∈
      cantorSet ratio) ∧
      ((1 - ratio) * (if digit.2 then 1 else 0) + ratio * (wordMap ratio rest point).2 ∈
      cantorSet ratio)
    constructor
    · rw [cantorSet_selfsimilar hnonnegative hless]
      cases h : digit.1
      · simp only [Bool.false_eq_true, if_false, mul_zero, zero_add]
        exact Or.inl ⟨_, ih.1, rfl⟩
      · simp only [if_true, mul_one]
        exact Or.inr ⟨_, ih.1, rfl⟩
    · rw [cantorSet_selfsimilar hnonnegative hless]
      cases h : digit.2
      · simp only [Bool.false_eq_true, if_false, mul_zero, zero_add]
        exact Or.inl ⟨_, ih.2, rfl⟩
      · simp only [if_true, mul_one]
        exact Or.inr ⟨_, ih.2, rfl⟩

theorem isCompact_cantorDust {ratio : ℝ} (hnonnegative : 0 ≤ ratio) (hless : ratio < 1) :
    IsCompact (cantorDust ratio) :=
  (isCompact_cantorSet hnonnegative hless).prod (isCompact_cantorSet hnonnegative hless)

theorem cantorDust_nonempty (ratio : ℝ) : (cantorDust ratio).Nonempty :=
  ⟨(0, 0), zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩

/-- The cylinder is the actual image of the Cantor dust, not just its square hull. -/
def wordCylinder (ratio : ℝ) (word : List (Bool × Bool)) : Set (ℝ × ℝ) :=
  wordMap ratio word '' cantorDust ratio

theorem isCompact_wordCylinder {ratio : ℝ} (hnonnegative : 0 ≤ ratio) (hless : ratio < 1)
    (word : List (Bool × Bool)) : IsCompact (wordCylinder ratio word) :=
  (isCompact_cantorDust hnonnegative hless).image (continuous_wordMap ratio word)

theorem wordCylinder_nonempty (ratio : ℝ) (word : List (Bool × Bool)) :
    (wordCylinder ratio word).Nonempty := (cantorDust_nonempty ratio).image _

theorem wordCylinder_append_subset {ratio : ℝ} (hnonnegative : 0 ≤ ratio) (hless : ratio < 1)
    (first second : List (Bool × Bool)) :
    wordCylinder ratio (first ++ second) ⊆ wordCylinder ratio first := by
  rintro point ⟨tail, htail, rfl⟩
  exact ⟨wordMap ratio second tail, wordMap_mem_dust hnonnegative hless second htail,
    (wordMap_append ratio first second tail).symm⟩

theorem wordCylinder_subset_dust {ratio : ℝ} (hnonnegative : 0 ≤ ratio) (hless : ratio < 1)
    (word : List (Bool × Bool)) : wordCylinder ratio word ⊆ cantorDust ratio := by
  rintro point ⟨tail, htail, rfl⟩
  exact wordMap_mem_dust hnonnegative hless word htail

theorem dust_dist_le_one {ratio : ℝ} (hnonnegative : 0 ≤ ratio) (hless : ratio < 1)
    {first second : ℝ × ℝ} (hfirst : first ∈ cantorDust ratio)
    (hsecond : second ∈ cantorDust ratio) : dist first second ≤ 1 := by
  have first_x := cantorSet_subset_unitInterval hnonnegative hless hfirst.1
  have first_y := cantorSet_subset_unitInterval hnonnegative hless hfirst.2
  have second_x := cantorSet_subset_unitInterval hnonnegative hless hsecond.1
  have second_y := cantorSet_subset_unitInterval hnonnegative hless hsecond.2
  rcases first_x with ⟨hfx0, hfx1⟩
  rcases first_y with ⟨hfy0, hfy1⟩
  rcases second_x with ⟨hsx0, hsx1⟩
  rcases second_y with ⟨hsy0, hsy1⟩
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq]
  constructor <;> rw [abs_le] <;> constructor <;> linarith

theorem wordCylinder_dist_le {ratio : ℝ} (hnonnegative : 0 ≤ ratio) (hless : ratio < 1)
    (word : List (Bool × Bool)) {first second : ℝ × ℝ}
    (hfirst : first ∈ wordCylinder ratio word) (hsecond : second ∈ wordCylinder ratio word) :
    dist first second ≤ ratio ^ word.length := by
  rcases hfirst with ⟨first, hfirst, rfl⟩
  rcases hsecond with ⟨second, hsecond, rfl⟩
  rw [wordMap_distance, abs_of_nonneg hnonnegative]
  exact mul_le_of_le_one_right (pow_nonneg hnonnegative _) (dust_dist_le_one hnonnegative hless hfirst hsecond)

/-- Explicit common-prefix divergence is the finite-word incomparability used
by the strict-return criterion. -/
def WordsDiverge (first second : List (Bool × Bool)) : Prop :=
  ∃ common firstDigit secondDigit firstRest secondRest,
    firstDigit ≠ secondDigit ∧ first = common ++ firstDigit :: firstRest ∧
      second = common ++ secondDigit :: secondRest

theorem digit_coordinate_gap {ratio first second : ℝ}
    (hnonnegative : 0 ≤ ratio) (hfirst : first ∈ Set.Icc (0 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (0 : ℝ) 1)
    (firstDigit secondDigit : Bool) (different : firstDigit ≠ secondDigit) :
    1 - 2 * ratio ≤
      |((1 - ratio) * (if firstDigit then 1 else 0) + ratio * first) -
        ((1 - ratio) * (if secondDigit then 1 else 0) + ratio * second)| := by
  rcases hfirst with ⟨hfirst0, hfirst1⟩
  rcases hsecond with ⟨hsecond0, hsecond1⟩
  cases firstDigit <;> cases secondDigit
  · exact False.elim (different rfl)
  · simp only [Bool.false_eq_true, if_false, if_true, mul_zero, mul_one, zero_add]
    apply le_trans _ (neg_le_abs _)
    nlinarith
  · simp only [Bool.false_eq_true, if_false, if_true, mul_zero, mul_one, zero_add]
    apply le_trans _ (le_abs_self _)
    nlinarith
  · exact False.elim (different rfl)

theorem first_digit_distance_gap {ratio : ℝ} (hnonnegative : 0 ≤ ratio) (hless : ratio < 1)
    (firstDigit secondDigit : Bool × Bool) (different : firstDigit ≠ secondDigit)
    {first second : ℝ × ℝ} (hfirst : first ∈ cantorDust ratio)
    (hsecond : second ∈ cantorDust ratio) :
    1 - 2 * ratio ≤ dist (wordMap ratio [firstDigit] first) (wordMap ratio [secondDigit] second) := by
  have different_coordinate : firstDigit.1 ≠ secondDigit.1 ∨ firstDigit.2 ≠ secondDigit.2 := by
    by_contra h
    push_neg at h
    exact different (Prod.ext h.1 h.2)
  rw [Prod.dist_eq]
  rcases different_coordinate with hx | hy
  · apply le_trans _ (le_max_left _ _)
    exact digit_coordinate_gap hnonnegative
      (cantorSet_subset_unitInterval hnonnegative hless hfirst.1)
      (cantorSet_subset_unitInterval hnonnegative hless hsecond.1) _ _ hx
  · apply le_trans _ (le_max_right _ _)
    exact digit_coordinate_gap hnonnegative
      (cantorSet_subset_unitInterval hnonnegative hless hfirst.2)
      (cantorSet_subset_unitInterval hnonnegative hless hsecond.2) _ _ hy

/-- Incomparable word cylinders have a uniform gap at every bounded depth. -/
theorem diverging_words_distance_gap {ratio : ℝ} (hpositive : 0 < ratio)
    (hless : ratio < 1 / 2) (firstWord secondWord : List (Bool × Bool))
    (diverge : WordsDiverge firstWord secondWord) (maxDepth : ℕ)
    (hdepth : firstWord.length ≤ maxDepth)
    {first second : ℝ × ℝ} (hfirst : first ∈ cantorDust ratio)
    (hsecond : second ∈ cantorDust ratio) :
    (1 - 2 * ratio) * ratio ^ maxDepth ≤
      dist (wordMap ratio firstWord first) (wordMap ratio secondWord second) := by
  obtain ⟨common, firstDigit, secondDigit, firstRest, secondRest,
    hdifferent, rfl, rfl⟩ := diverge
  have hless_one : ratio < 1 := by linarith
  have common_bound : common.length ≤ maxDepth := by
    simp only [List.length_append, List.length_cons] at hdepth
    omega
  rw [wordMap_append, wordMap_append, wordMap_distance, abs_of_pos hpositive]
  have hgap := first_digit_distance_gap hpositive.le hless_one firstDigit secondDigit hdifferent
    (wordMap_mem_dust hpositive.le hless_one firstRest hfirst)
    (wordMap_mem_dust hpositive.le hless_one secondRest hsecond)
  change 1 - 2 * ratio ≤ dist (wordMap ratio (firstDigit :: firstRest) first)
    (wordMap ratio (secondDigit :: secondRest) second) at hgap
  calc
    (1 - 2 * ratio) * ratio ^ maxDepth ≤ (1 - 2 * ratio) * ratio ^ common.length :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hpositive.le hless_one.le common_bound) (by linarith)
    _ = ratio ^ common.length * (1 - 2 * ratio) := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hgap (pow_nonneg hpositive.le _)

end LambdaCantor.Last
