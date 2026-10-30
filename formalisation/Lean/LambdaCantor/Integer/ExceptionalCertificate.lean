import LambdaCantor.Integer.ExceptionalReturnSemantics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace LambdaCantor.Integer.Exceptional

structure Piece where
  lower : ℤ
  upper : ℤ
  rule : ℕ
  firstRef : ℕ
  secondRef : ℕ
  firstDigit : Fin 4
  secondDigit : Fin 4
  deriving DecidableEq, Repr, Inhabited

structure Node where
  two : Bool
  depth : ℕ
  lower : ℤ
  upper : ℤ
  pieces : List Piece
  deriving DecidableEq, Repr, Inhabited

def coversFrom (position upper : ℤ) : List Piece → Bool
  | [] => false
  | piece :: remaining => decide (piece.lower ≤ position ∧ position ≤ piece.upper) &&
      (decide (upper ≤ piece.upper) || coversFrom piece.upper upper remaining)

def pieceValid (offsets : Fin 4 → ℤ) (nodes : Array Node) (index : ℕ)
    (node : Node) (piece : Piece) : Prop :=
  piece.lower ≤ piece.upper ∧ piece.firstRef < index ∧
  let first := nodes.getD piece.firstRef default
  if piece.rule = 0 then
    first.two = node.two ∧ first.depth ≤ node.depth ∧
      first.lower ≤ piece.lower ∧ piece.upper ≤ first.upper
  else if piece.rule = 1 then
    first.two = node.two ∧ first.depth + 1 ≤ node.depth ∧
      first.lower ≤ 3 * piece.lower - offsets piece.firstDigit ∧
      3 * piece.upper - offsets piece.firstDigit ≤ first.upper
  else
    piece.rule = 2 ∧ node.two = true ∧ first.two = false ∧
      piece.secondRef < index ∧
      let second := nodes.getD piece.secondRef default
      second.two = false ∧ first.depth + 1 ≤ node.depth ∧ second.depth + 1 ≤ node.depth ∧
        piece.firstDigit ≠ piece.secondDigit ∧
        first.lower ≤ 3 * piece.lower - offsets piece.firstDigit ∧
        3 * piece.upper - offsets piece.firstDigit ≤ first.upper ∧
        second.lower ≤ 3 * piece.lower - offsets piece.secondDigit ∧
        3 * piece.upper - offsets piece.secondDigit ≤ second.upper

instance (offsets : Fin 4 → ℤ) (nodes : Array Node) (index : ℕ)
    (node : Node) (piece : Piece) : Decidable (pieceValid offsets nodes index node piece) := by
  unfold pieceValid
  infer_instance

def nodeValid (offsets : Fin 4 → ℤ) (innerIntervals : List (ℤ × ℤ))
    (nodes : Array Node) (index : ℕ) : Prop :=
  let node := nodes.getD index default
  node.lower ≤ node.upper ∧
  if node.pieces = [] then
    node.two = false ∧ node.depth = 0 ∧
      ∃ interval ∈ innerIntervals, interval.1 ≤ node.lower ∧ node.upper ≤ interval.2
  else
    coversFrom node.lower node.upper node.pieces = true ∧
      ∀ piece ∈ node.pieces, pieceValid offsets nodes index node piece

instance (offsets : Fin 4 → ℤ) (innerIntervals : List (ℤ × ℤ))
    (nodes : Array Node) (index : ℕ) : Decidable (nodeValid offsets innerIntervals nodes index) := by
  unfold nodeValid
  infer_instance

def checkCertificate (denominator : ℤ) (offsets : Fin 4 → ℤ)
    (innerIntervals : List (ℤ × ℤ)) (nodes : Array Node) : Bool :=
  decide (0 < denominator) &&
    (List.range nodes.size).all (fun index => decide (nodeValid offsets innerIntervals nodes index))

def scaledInterval (denominator lower upper : ℤ) : Set ℝ :=
  {level | (lower : ℝ) ≤ denominator * level ∧ denominator * level ≤ upper}

def innerTarget (denominator : ℤ) (innerIntervals : List (ℤ × ℤ)) : Set ℝ :=
  {level | ∃ interval ∈ innerIntervals, level ∈ scaledInterval denominator interval.1 interval.2}

def returnClaim (denominator : ℤ) (offsets : Fin 4 → ℤ)
    (innerIntervals : List (ℤ × ℤ)) (two : Bool) (depth : ℕ) (level : ℝ) : Prop :=
    if two then
      TwoReturns (fun digit => (offsets digit : ℝ) / denominator)
        (innerTarget denominator innerIntervals) depth level
    else
      OneReturn (fun digit => (offsets digit : ℝ) / denominator)
        (innerTarget denominator innerIntervals) depth level

def nodeSemantics (denominator : ℤ) (offsets : Fin 4 → ℤ)
    (innerIntervals : List (ℤ × ℤ)) (node : Node) : Prop :=
  ∀ level ∈ scaledInterval denominator node.lower node.upper,
    returnClaim denominator offsets innerIntervals node.two node.depth level

theorem returnClaim_mono {denominator : ℤ} {offsets : Fin 4 → ℤ}
    {innerIntervals : List (ℤ × ℤ)} {two : Bool} {depth later : ℕ} {level : ℝ}
    (claim : returnClaim denominator offsets innerIntervals two depth level)
    (bound : depth ≤ later) : returnClaim denominator offsets innerIntervals two later level := by
  cases two
  · exact OneReturn.mono claim bound
  · exact TwoReturns.mono claim bound

theorem returnClaim_lift {denominator : ℤ} {offsets : Fin 4 → ℤ}
    {innerIntervals : List (ℤ × ℤ)} {two : Bool} {depth : ℕ} {level : ℝ}
    (digit : Fin 4)
    (claim : returnClaim denominator offsets innerIntervals two depth
      (3 * level - (offsets digit : ℝ) / denominator)) :
    returnClaim denominator offsets innerIntervals two (depth + 1) level := by
  cases two
  · exact OneReturn.lift digit claim
  · exact TwoReturns.lift digit claim

theorem coversFrom_sound (pieces : List Piece) (position upper : ℤ)
    (covered : coversFrom position upper pieces = true)
    (value : ℝ) (lower_bound : (position : ℝ) ≤ value) (upper_bound : value ≤ upper) :
    ∃ piece ∈ pieces, (piece.lower : ℝ) ≤ value ∧ value ≤ piece.upper := by
  induction pieces generalizing position with
  | nil => simp [coversFrom] at covered
  | cons piece remaining inductionHypothesis =>
    simp only [coversFrom, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at covered
    have first_lower : (piece.lower : ℝ) ≤ position := by exact_mod_cast covered.1.1
    by_cases inside : value ≤ piece.upper
    · exact ⟨piece, by simp, first_lower.trans lower_bound, inside⟩
    · rcases covered.2 with finished | continued
      · have last_bound : (upper : ℝ) ≤ piece.upper := by exact_mod_cast finished
        exact False.elim (inside (upper_bound.trans last_bound))
      · obtain ⟨later, membership, bounds⟩ := inductionHypothesis piece.upper continued
          (le_of_lt (lt_of_not_ge inside))
        exact ⟨later, by simp [membership], bounds⟩

theorem transformed_interval (denominator lower upper childLower childUpper offset : ℤ)
    (positive : 0 < denominator) (level : ℝ)
    (inside : level ∈ scaledInterval denominator lower upper)
    (lower_bound : childLower ≤ 3 * lower - offset)
    (upper_bound : 3 * upper - offset ≤ childUpper) :
    3 * level - (offset : ℝ) / denominator ∈
      scaledInterval denominator childLower childUpper := by
  have nonzero : (denominator : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt positive)
  have identity : (denominator : ℝ) * (3 * level - (offset : ℝ) / denominator) =
      3 * (denominator * level) - offset := by field_simp [nonzero] <;> ring
  have lower_real : (childLower : ℝ) ≤ 3 * lower - offset := by exact_mod_cast lower_bound
  have upper_real : (3 : ℝ) * upper - offset ≤ childUpper := by exact_mod_cast upper_bound
  change (lower : ℝ) ≤ denominator * level ∧ denominator * level ≤ upper at inside
  change (childLower : ℝ) ≤ (denominator : ℝ) * (3 * level - (offset : ℝ) / denominator) ∧
    (denominator : ℝ) * (3 * level - (offset : ℝ) / denominator) ≤ (childUpper : ℝ)
  rw [identity]
  constructor <;> linarith [inside.1, inside.2]

theorem pieceValid_sound (denominator : ℤ) (positive : 0 < denominator)
    (offsets : Fin 4 → ℤ) (innerIntervals : List (ℤ × ℤ))
    (nodes : Array Node) (index : ℕ) (node : Node) (piece : Piece)
    (valid : pieceValid offsets nodes index node piece)
    (earlier : ∀ reference < index,
      nodeSemantics denominator offsets innerIntervals (nodes.getD reference default))
    (level : ℝ) (inside : level ∈ scaledInterval denominator piece.lower piece.upper) :
    returnClaim denominator offsets innerIntervals node.two node.depth level := by
  rcases valid with ⟨ordered, first_reference, rule_valid⟩
  dsimp only at rule_valid
  have first_semantics := earlier piece.firstRef first_reference
  by_cases carry : piece.rule = 0
  · simp only [carry, if_pos] at rule_valid
    obtain ⟨same_mode, depth_bound, lower_bound, upper_bound⟩ := rule_valid
    have lower_real : ((nodes.getD piece.firstRef default).lower : ℝ) ≤ piece.lower := by
      exact_mod_cast lower_bound
    have upper_real : (piece.upper : ℝ) ≤ (nodes.getD piece.firstRef default).upper := by
      exact_mod_cast upper_bound
    have child := first_semantics level
      ⟨lower_real.trans inside.1, inside.2.trans upper_real⟩
    rw [same_mode] at child
    exact returnClaim_mono child depth_bound
  · by_cases lift : piece.rule = 1
    · simp only [carry, lift, if_false, if_true] at rule_valid
      obtain ⟨same_mode, depth_bound, lower_bound, upper_bound⟩ := rule_valid
      have child := first_semantics (3 * level - (offsets piece.firstDigit : ℝ) / denominator)
        (transformed_interval denominator piece.lower piece.upper _ _ _ positive level inside
          lower_bound upper_bound)
      rw [same_mode] at child
      exact returnClaim_mono (returnClaim_lift piece.firstDigit child) depth_bound
    · simp only [carry, lift, if_false] at rule_valid
      obtain ⟨branch, node_mode, first_mode, second_reference, second_mode,
        first_depth, second_depth, different, first_lower, first_upper, second_lower, second_upper⟩ := rule_valid
      have first_child := first_semantics
        (3 * level - (offsets piece.firstDigit : ℝ) / denominator)
        (transformed_interval denominator piece.lower piece.upper _ _ _ positive level inside
          first_lower first_upper)
      have second_child := earlier piece.secondRef second_reference
        (3 * level - (offsets piece.secondDigit : ℝ) / denominator)
        (transformed_interval denominator piece.lower piece.upper _ _ _ positive level inside
          second_lower second_upper)
      simp only [returnClaim, first_mode, if_false] at first_child
      simp only [returnClaim, second_mode, if_false] at second_child
      simp only [returnClaim, node_mode, if_true]
      have returns := twoReturns_of_distinct_children piece.firstDigit piece.secondDigit different
        (OneReturn.mono first_child
          (le_max_left (nodes.getD piece.firstRef default).depth (nodes.getD piece.secondRef default).depth))
        (OneReturn.mono second_child
          (le_max_right (nodes.getD piece.firstRef default).depth (nodes.getD piece.secondRef default).depth))
      exact TwoReturns.mono returns (by omega)

theorem nodeValid_sound (denominator : ℤ) (positive : 0 < denominator)
    (offsets : Fin 4 → ℤ) (innerIntervals : List (ℤ × ℤ))
    (nodes : Array Node) (index : ℕ)
    (valid : nodeValid offsets innerIntervals nodes index)
    (earlier : ∀ reference < index,
      nodeSemantics denominator offsets innerIntervals (nodes.getD reference default)) :
    nodeSemantics denominator offsets innerIntervals (nodes.getD index default) := by
  intro level inside
  rcases valid with ⟨ordered, rule_valid⟩
  by_cases seed : (nodes.getD index default).pieces = []
  · simp only [seed, if_true] at rule_valid
    obtain ⟨mode, depth, interval, membership, lower_bound, upper_bound⟩ := rule_valid
    simp only [returnClaim, mode, if_false, depth]
    apply oneReturn_stop
    refine ⟨interval, membership, ?_, ?_⟩
    · have bound : (interval.1 : ℝ) ≤ (nodes.getD index default).lower := by exact_mod_cast lower_bound
      exact bound.trans inside.1
    · have bound : ((nodes.getD index default).upper : ℝ) ≤ interval.2 := by exact_mod_cast upper_bound
      exact inside.2.trans bound
  · simp only [seed, if_false] at rule_valid
    obtain ⟨piece, membership, piece_bounds⟩ := coversFrom_sound
      (nodes.getD index default).pieces (nodes.getD index default).lower
      (nodes.getD index default).upper rule_valid.1 (denominator * level) inside.1 inside.2
    exact pieceValid_sound denominator positive offsets innerIntervals nodes index
      (nodes.getD index default) piece (rule_valid.2 piece membership) earlier level piece_bounds

/-- Every node of an accepted finite certificate has the declared real return semantics. -/
theorem checkCertificate_sound (denominator : ℤ) (offsets : Fin 4 → ℤ)
    (innerIntervals : List (ℤ × ℤ)) (nodes : Array Node)
    (accepted : checkCertificate denominator offsets innerIntervals nodes = true) :
    ∀ index < nodes.size,
      nodeSemantics denominator offsets innerIntervals (nodes.getD index default) := by
  simp only [checkCertificate, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at accepted
  have positive : 0 < denominator := accepted.1
  intro index
  induction index using Nat.strong_induction_on with
  | h index inductionHypothesis =>
    intro bound
    apply nodeValid_sound denominator positive offsets innerIntervals nodes index
    · exact accepted.2 index (List.mem_range.mpr bound)
    · intro reference smaller
      exact inductionHypothesis reference smaller (lt_trans smaller bound)

def coversSomewhere (lower upper : ℤ) : List Piece → Bool
  | [] => false
  | piece :: remaining => coversFrom lower upper (piece :: remaining) ||
      coversSomewhere lower upper remaining

theorem coversSomewhere_sound (pieces : List Piece) (lower upper : ℤ)
    (covered : coversSomewhere lower upper pieces = true)
    (value : ℝ) (lower_bound : (lower : ℝ) ≤ value) (upper_bound : value ≤ upper) :
    ∃ piece ∈ pieces, (piece.lower : ℝ) ≤ value ∧ value ≤ piece.upper := by
  induction pieces with
  | nil => simp [coversSomewhere] at covered
  | cons piece remaining inductionHypothesis =>
    simp only [coversSomewhere, Bool.or_eq_true] at covered
    rcases covered with first | later
    · exact coversFrom_sound (piece :: remaining) lower upper first value lower_bound upper_bound
    · obtain ⟨found, membership, bounds⟩ := inductionHypothesis later
      exact ⟨found, by simp [membership], bounds⟩

def rootPiece (nodes : Array Node) (reference : ℕ) : Piece :=
  ⟨(nodes.getD reference default).lower, (nodes.getD reference default).upper,
    0, reference, 0, 0, 0⟩

def checkRoots (outerIntervals : List (ℤ × ℤ)) (nodes : Array Node)
    (roots : List ℕ) (maximumDepth : ℕ) : Bool :=
  roots.all (fun reference => decide (reference < nodes.size ∧
    (nodes.getD reference default).two = true ∧ (nodes.getD reference default).depth ≤ maximumDepth)) &&
  outerIntervals.all (fun interval =>
    coversSomewhere interval.1 interval.2 (roots.map (rootPiece nodes)))

/-- Checking the DAG and its designated roots proves the two separated return words
for every real level in the entire outer interval union. -/
theorem checked_roots_sound (denominator : ℤ) (offsets : Fin 4 → ℤ)
    (innerIntervals outerIntervals : List (ℤ × ℤ)) (nodes : Array Node)
    (roots : List ℕ) (maximumDepth : ℕ)
    (certificate : checkCertificate denominator offsets innerIntervals nodes = true)
    (covered : checkRoots outerIntervals nodes roots maximumDepth = true) :
    ∀ level ∈ innerTarget denominator outerIntervals,
      TwoReturns (fun digit => (offsets digit : ℝ) / denominator)
        (innerTarget denominator innerIntervals) maximumDepth level := by
  have semantics := checkCertificate_sound denominator offsets innerIntervals nodes certificate
  simp only [checkRoots, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at covered
  intro level membership
  obtain ⟨interval, interval_member, lower_bound, upper_bound⟩ := membership
  obtain ⟨piece, piece_member, piece_bounds⟩ := coversSomewhere_sound
    (roots.map (rootPiece nodes)) interval.1 interval.2 (covered.2 interval interval_member)
    (denominator * level) lower_bound upper_bound
  obtain ⟨reference, reference_member, rfl⟩ := List.mem_map.mp piece_member
  have root_valid := covered.1 reference reference_member
  have returns := semantics reference root_valid.1 level piece_bounds
  simp only [returnClaim, root_valid.2.1, if_true] at returns
  exact TwoReturns.mono returns root_valid.2.2

end LambdaCantor.Integer.Exceptional
