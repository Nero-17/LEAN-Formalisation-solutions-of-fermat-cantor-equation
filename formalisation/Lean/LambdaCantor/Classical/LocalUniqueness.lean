import LambdaCantor.Classical.Cylinders

noncomputable section
namespace LambdaCantor.Classical

def ternaryChild (digit : Bool) (tail : ℝ) : ℝ :=
  ((if digit then 2 else 0) + tail) / 3

theorem ternaryChild_bounds (digit : Bool) {tail : ℝ}
    (bounds : tail ∈ Set.Icc (0 : ℝ) 1) : ternaryChild digit tail ∈ Set.Icc (0 : ℝ) 1 := by
  cases digit <;> simp only [ternaryChild, Bool.false_eq_true, if_false, if_true]
    <;> constructor <;> linarith [bounds.1, bounds.2]

theorem ternaryChild_member (digit : Bool) {tail : ℝ}
    (membership : tail ∈ cantorSet (1 / 3)) : ternaryChild digit tail ∈ cantorSet (1 / 3) := by
  rw [cantorSet_third_eq] at membership ⊢
  cases digit
  · simpa [ternaryChild] using cantor_prepend_zero membership
  · simpa [ternaryChild] using cantor_prepend_two membership

theorem ternaryChild_digit_unique (first second : Bool) (firstTail secondTail : ℝ)
    (first_bounds : firstTail ∈ Set.Icc (0 : ℝ) 1)
    (second_bounds : secondTail ∈ Set.Icc (0 : ℝ) 1)
    (same : ternaryChild first firstTail = ternaryChild second secondTail) : first = second := by
  cases first <;> cases second <;> simp_all [ternaryChild] <;>
    linarith [first_bounds.1, first_bounds.2, second_bounds.1, second_bounds.2]

def realDigit (slope : ℝ) (first second : Bool) : ℝ :=
  slope * (if first then 1 else 0) + (if second then 1 else 0)

theorem child_linear_corners (slope : ℝ) (first second : Bool) :
    (slope * ternaryChild first 0 + ternaryChild second 0) / 2 =
      realDigit slope first second / 3 ∧
    (slope * ternaryChild first 1 + ternaryChild second 1) / 2 =
      realDigit slope first second / 3 + (slope + 1) / 6 := by
  cases first <;> cases second <;> constructor <;> simp [realDigit, ternaryChild] <;> ring

/-- The exact Taylor error turns a trimmed linear child interval into a true crossing. -/
theorem trimmed_child_brackets (a b tailA tailB side : ℝ) (first second : Bool)
    (b_nonnegative : 0 ≤ b) (side_positive : 0 < side)
    (tailA_bounds : tailA ∈ Set.Icc (0 : ℝ) 1)
    (tailB_bounds : tailB ∈ Set.Icc (0 : ℝ) 1)
    (lower : realDigit ((6336 + a) / (9 * (566 + b))) first second / 3 +
        (5 / 10188 : ℝ) * side < (((6336 + a) / (9 * (566 + b))) * tailA + tailB) / 2)
    (upper : (((6336 + a) / (9 * (566 + b))) * tailA + tailB) / 2 <
        realDigit ((6336 + a) / (9 * (566 + b))) first second / 3 +
          (((6336 + a) / (9 * (566 + b))) + 1) / 6 - (5 / 10188 : ℝ) * side) :
    cylinderPolynomial (a + side * (ternaryChild first 0 - tailA))
      (b + side * (ternaryChild second 0 - tailB)) < cylinderPolynomial a b ∧
    cylinderPolynomial a b <
      cylinderPolynomial (a + side * (ternaryChild first 1 - tailA))
        (b + side * (ternaryChild second 1 - tailB)) := by
  have b_positive : 0 < 566 + b := by linarith
  have denominator_positive : 0 < 36 * (566 + b) * side := by positivity
  have corners := child_linear_corners ((6336 + a) / (9 * (566 + b))) first second
  have lower_expansion := cylinder_quadratic_expansion a b (ternaryChild first 0)
    (ternaryChild second 0) tailA tailB side (ne_of_gt b_positive) (ne_of_gt side_positive)
  have upper_expansion := cylinder_quadratic_expansion a b (ternaryChild first 1)
    (ternaryChild second 1) tailA tailB side (ne_of_gt b_positive) (ne_of_gt side_positive)
  have lower_remainder := cylinder_remainder_bounds b (ternaryChild first 0)
    (ternaryChild second 0) tailA tailB side b_nonnegative side_positive.le
    (ternaryChild_bounds first (by norm_num)) (ternaryChild_bounds second (by norm_num))
    tailA_bounds tailB_bounds
  have upper_remainder := cylinder_remainder_bounds b (ternaryChild first 1)
    (ternaryChild second 1) tailA tailB side b_nonnegative side_positive.le
    (ternaryChild_bounds first (by norm_num)) (ternaryChild_bounds second (by norm_num))
    tailA_bounds tailB_bounds
  rw [corners.1] at lower_expansion
  rw [corners.2] at upper_expansion
  constructor
  · have quotient_negative :
        (cylinderPolynomial (a + side * (ternaryChild first 0 - tailA))
          (b + side * (ternaryChild second 0 - tailB)) - cylinderPolynomial a b) /
          (36 * (566 + b) * side) < 0 := by linarith [lower_remainder.2]
    have numerator_negative := (div_lt_iff₀ denominator_positive).mp quotient_negative
    nlinarith
  · have quotient_positive : 0 <
        (cylinderPolynomial (a + side * (ternaryChild first 1 - tailA))
          (b + side * (ternaryChild second 1 - tailB)) - cylinderPolynomial a b) /
          (36 * (566 + b) * side) := by linarith [upper_remainder.1]
    have numerator_positive := (lt_div_iff₀ denominator_positive).mp quotient_positive
    nlinarith

theorem trimmed_child_level (u v a b tailA tailB side : ℝ) (first second : Bool)
    (u_nonnegative : 0 ≤ u) (v_nonnegative : 0 ≤ v)
    (side_positive : 0 < side) (u_upper : u + side ≤ 1) (v_upper : v + side ≤ 1)
    (tailA_bounds : tailA ∈ Set.Icc (0 : ℝ) 1)
    (tailB_bounds : tailB ∈ Set.Icc (0 : ℝ) 1)
    (first_decomposition : a = u + side * tailA)
    (second_decomposition : b = v + side * tailB)
    (lower : realDigit ((6336 + a) / (9 * (566 + b))) first second / 3 +
        (5 / 10188 : ℝ) * side < (((6336 + a) / (9 * (566 + b))) * tailA + tailB) / 2)
    (upper : (((6336 + a) / (9 * (566 + b))) * tailA + tailB) / 2 <
        realDigit ((6336 + a) / (9 * (566 + b))) first second / 3 +
          (((6336 + a) / (9 * (566 + b))) + 1) / 6 - (5 / 10188 : ℝ) * side) :
    ∃ nextA nextB : ℝ, nextA ∈ cantorSet (1 / 3) ∧ nextB ∈ cantorSet (1 / 3) ∧
      cylinderPolynomial (u + side * ternaryChild first nextA)
        (v + side * ternaryChild second nextB) = cylinderPolynomial a b := by
  have b_nonnegative : 0 ≤ b := by nlinarith [mul_nonneg side_positive.le tailB_bounds.1]
  have brackets := trimmed_child_brackets a b tailA tailB side first second
    b_nonnegative side_positive tailA_bounds tailB_bounds lower upper
  have child_u_nonnegative : 0 ≤ u + side * ternaryChild first 0 := by
    cases first <;> simp [ternaryChild] <;> nlinarith
  have child_v_nonnegative : 0 ≤ v + side * ternaryChild second 0 := by
    cases second <;> simp [ternaryChild] <;> nlinarith
  have child_u_upper : u + side * ternaryChild first 0 + side / 3 ≤ 1 := by
    cases first <;> simp [ternaryChild] <;> nlinarith
  have child_v_upper : v + side * ternaryChild second 0 + side / 3 ≤ 1 := by
    cases second <;> simp [ternaryChild] <;> nlinarith
  have child_lower : cylinderPolynomial (u + side * ternaryChild first 0)
      (v + side * ternaryChild second 0) ≤ cylinderPolynomial a b := by
    have first_coordinate : a + side * (ternaryChild first 0 - tailA) =
        u + side * ternaryChild first 0 := by rw [first_decomposition]; ring
    have second_coordinate : b + side * (ternaryChild second 0 - tailB) =
        v + side * ternaryChild second 0 := by rw [second_decomposition]; ring
    simpa only [first_coordinate, second_coordinate] using brackets.1.le
  have child_upper : cylinderPolynomial a b ≤
      cylinderPolynomial (u + side * ternaryChild first 0 + side / 3)
        (v + side * ternaryChild second 0 + side / 3) := by
    have first_coordinate : a + side * (ternaryChild first 1 - tailA) =
        u + side * ternaryChild first 0 + side / 3 := by
      rw [first_decomposition]; unfold ternaryChild; ring
    have second_coordinate : b + side * (ternaryChild second 1 - tailB) =
        v + side * ternaryChild second 0 + side / 3 := by
      rw [second_decomposition]; unfold ternaryChild; ring
    simpa only [first_coordinate, second_coordinate] using brackets.2.le
  obtain ⟨nextA, nextB, first_member, second_member, value⟩ :=
    cylinder_cantor_level (u + side * ternaryChild first 0)
      (v + side * ternaryChild second 0) (side / 3) (cylinderPolynomial a b)
      child_u_nonnegative child_v_nonnegative (by positivity)
      child_u_upper child_v_upper child_lower child_upper
  refine ⟨nextA, nextB, ?_, ?_, ?_⟩
  · rw [cantorSet_third_eq]; exact first_member
  · rw [cantorSet_third_eq]; exact second_member
  · have first_coordinate : u + side * ternaryChild first 0 + side / 3 * nextA =
        u + side * ternaryChild first nextA := by unfold ternaryChild; ring
    have second_coordinate : v + side * ternaryChild second 0 + side / 3 * nextB =
        v + side * ternaryChild second nextB := by unfold ternaryChild; ring
    simpa only [first_coordinate, second_coordinate] using value

theorem unique_square_forces_label (u v a b tailA tailB side : ℝ)
    (originalFirst originalSecond competingFirst competingSecond : Bool)
    (originalNextA originalNextB : ℝ)
    (u_nonnegative : 0 ≤ u) (v_nonnegative : 0 ≤ v)
    (side_positive : 0 < side) (u_upper : u + side ≤ 1) (v_upper : v + side ≤ 1)
    (tailA_bounds : tailA ∈ Set.Icc (0 : ℝ) 1)
    (tailB_bounds : tailB ∈ Set.Icc (0 : ℝ) 1)
    (nextA_bounds : originalNextA ∈ Set.Icc (0 : ℝ) 1)
    (nextB_bounds : originalNextB ∈ Set.Icc (0 : ℝ) 1)
    (first_tail : tailA = ternaryChild originalFirst originalNextA)
    (second_tail : tailB = ternaryChild originalSecond originalNextB)
    (first_decomposition : a = u + side * tailA)
    (second_decomposition : b = v + side * tailB)
    (unique : ∀ first second : ℝ, first ∈ cantorSet (1 / 3) → second ∈ cantorSet (1 / 3) →
      cylinderPolynomial (u + side * first) (v + side * second) = cylinderPolynomial a b →
        u + side * first = a ∧ v + side * second = b)
    (lower : realDigit ((6336 + a) / (9 * (566 + b))) competingFirst competingSecond / 3 +
        (5 / 10188 : ℝ) * side < (((6336 + a) / (9 * (566 + b))) * tailA + tailB) / 2)
    (upper : (((6336 + a) / (9 * (566 + b))) * tailA + tailB) / 2 <
        realDigit ((6336 + a) / (9 * (566 + b))) competingFirst competingSecond / 3 +
          (((6336 + a) / (9 * (566 + b))) + 1) / 6 - (5 / 10188 : ℝ) * side) :
    originalFirst = competingFirst ∧ originalSecond = competingSecond := by
  obtain ⟨nextA, nextB, first_member, second_member, value⟩ :=
    trimmed_child_level u v a b tailA tailB side competingFirst competingSecond
      u_nonnegative v_nonnegative side_positive u_upper v_upper tailA_bounds tailB_bounds
      first_decomposition second_decomposition lower upper
  have equality := unique (ternaryChild competingFirst nextA) (ternaryChild competingSecond nextB)
    (ternaryChild_member competingFirst first_member) (ternaryChild_member competingSecond second_member)
    value
  have first_bounds := LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) first_member
  have second_bounds := LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) second_member
  constructor
  · apply ternaryChild_digit_unique originalFirst competingFirst originalNextA nextA
      nextA_bounds first_bounds
    rw [← first_tail]
    apply mul_left_cancel₀ (ne_of_gt side_positive)
    linarith [equality.1]
  · apply ternaryChild_digit_unique originalSecond competingSecond originalNextB nextB
      nextB_bounds second_bounds
    rw [← second_tail]
    apply mul_left_cancel₀ (ne_of_gt side_positive)
    linarith [equality.2]

def exclusiveLower (slope : ℝ) (first second : Bool) : ℝ :=
  if first then (if second then (3 * slope + 1) / 6 else (slope + 3) / 6)
  else if second then (slope + 1) / 6 else 0

def exclusiveUpper (slope : ℝ) (first second : Bool) : ℝ :=
  if first then (if second then (slope + 1) / 2 else (slope + 1) / 3)
  else if second then slope / 3 else 1 / 3

theorem linear_child_bounds (slope : ℝ) (first second : Bool) (nextA nextB : ℝ)
    (slope_nonnegative : 0 ≤ slope)
    (nextA_bounds : nextA ∈ Set.Icc (0 : ℝ) 1)
    (nextB_bounds : nextB ∈ Set.Icc (0 : ℝ) 1) :
    realDigit slope first second / 3 ≤
        (slope * ternaryChild first nextA + ternaryChild second nextB) / 2 ∧
    (slope * ternaryChild first nextA + ternaryChild second nextB) / 2 ≤
      realDigit slope first second / 3 + (slope + 1) / 6 := by
  have lower_product := mul_nonneg slope_nonnegative nextA_bounds.1
  have upper_product := mul_le_mul_of_nonneg_left nextA_bounds.2 slope_nonnegative
  cases first <;> cases second <;> simp only [ternaryChild, realDigit, if_true,
    Bool.false_eq_true, if_false] <;> constructor <;> nlinarith [nextB_bounds.1, nextB_bounds.2]

/-- The endpoint-safe exclusive-domain estimate derived from actual uniqueness. -/
theorem unique_square_exclusive (u v a b tailA tailB side : ℝ)
    (originalFirst originalSecond : Bool) (originalNextA originalNextB : ℝ)
    (u_nonnegative : 0 ≤ u) (v_nonnegative : 0 ≤ v)
    (side_positive : 0 < side) (u_upper : u + side ≤ 1) (v_upper : v + side ≤ 1)
    (tailA_bounds : tailA ∈ Set.Icc (0 : ℝ) 1)
    (tailB_bounds : tailB ∈ Set.Icc (0 : ℝ) 1)
    (nextA_bounds : originalNextA ∈ Set.Icc (0 : ℝ) 1)
    (nextB_bounds : originalNextB ∈ Set.Icc (0 : ℝ) 1)
    (first_tail : tailA = ternaryChild originalFirst originalNextA)
    (second_tail : tailB = ternaryChild originalSecond originalNextB)
    (first_decomposition : a = u + side * tailA)
    (second_decomposition : b = v + side * tailB)
    (unique : ∀ first second : ℝ, first ∈ cantorSet (1 / 3) → second ∈ cantorSet (1 / 3) →
      cylinderPolynomial (u + side * first) (v + side * second) = cylinderPolynomial a b →
        u + side * first = a ∧ v + side * second = b)
    (slope_nonnegative : 0 ≤ (6336 + a) / (9 * (566 + b)))
    (small_error : (5 / 10188 : ℝ) * side < 1 / 3)
    (small_gap : (5 / 10188 : ℝ) * side < ((6336 + a) / (9 * (566 + b)) - 1) / 3) :
    exclusiveLower ((6336 + a) / (9 * (566 + b))) originalFirst originalSecond -
        (5 / 10188 : ℝ) * side ≤ (((6336 + a) / (9 * (566 + b))) * tailA + tailB) / 2 ∧
    (((6336 + a) / (9 * (566 + b))) * tailA + tailB) / 2 ≤
      exclusiveUpper ((6336 + a) / (9 * (566 + b))) originalFirst originalSecond +
        (5 / 10188 : ℝ) * side := by
  have own_bounds := linear_child_bounds ((6336 + a) / (9 * (566 + b)))
    originalFirst originalSecond originalNextA originalNextB slope_nonnegative
    nextA_bounds nextB_bounds
  rw [← first_tail, ← second_tail] at own_bounds
  have excludes (competingFirst competingSecond : Bool)
      (different : (originalFirst, originalSecond) ≠ (competingFirst, competingSecond)) :
      ¬ (realDigit ((6336 + a) / (9 * (566 + b))) competingFirst competingSecond / 3 +
          (5 / 10188 : ℝ) * side < (((6336 + a) / (9 * (566 + b))) * tailA + tailB) / 2 ∧
        (((6336 + a) / (9 * (566 + b))) * tailA + tailB) / 2 <
          realDigit ((6336 + a) / (9 * (566 + b))) competingFirst competingSecond / 3 +
            (((6336 + a) / (9 * (566 + b))) + 1) / 6 - (5 / 10188 : ℝ) * side) := by
    rintro ⟨lower, upper⟩
    have equal_labels := unique_square_forces_label u v a b tailA tailB side
      originalFirst originalSecond competingFirst competingSecond originalNextA originalNextB
      u_nonnegative v_nonnegative side_positive u_upper v_upper tailA_bounds tailB_bounds
      nextA_bounds nextB_bounds first_tail second_tail first_decomposition second_decomposition
      unique lower upper
    exact different (Prod.ext equal_labels.1 equal_labels.2)
  have error_nonnegative : 0 ≤ (5 / 10188 : ℝ) * side := by positivity
  cases originalFirst <;> cases originalSecond
  · simp only [exclusiveLower, exclusiveUpper, Bool.false_eq_true, if_false, zero_sub]
    apply isolated_zero_interval _ _ _ error_nonnegative small_error
    · simpa [realDigit] using own_bounds
    · simpa [realDigit] using excludes false true (by decide)
  · simp only [exclusiveLower, exclusiveUpper, Bool.false_eq_true, if_false, if_true]
    apply isolated_one_interval _ _ _ error_nonnegative small_error small_gap
    · simpa [realDigit] using own_bounds
    · simpa [realDigit] using excludes false false (by decide)
    · simpa [realDigit] using excludes true false (by decide)
  · simp only [exclusiveLower, exclusiveUpper, Bool.false_eq_true, if_false, if_true]
    apply isolated_r_interval _ _ _ error_nonnegative small_error small_gap
    · simpa [realDigit] using own_bounds
    · simpa [realDigit] using excludes false true (by decide)
    · intro trimmed
      apply excludes true true (by decide)
      constructor
      · simpa [realDigit] using trimmed.1
      · simp only [realDigit, if_true, mul_one]
        linarith [trimmed.2]
  · simp only [exclusiveLower, exclusiveUpper, if_true]
    apply isolated_top_interval _ _ _ error_nonnegative small_error
    · constructor
      · simpa [realDigit] using own_bounds.1
      · have bound := own_bounds.2
        simp only [realDigit, if_true, mul_one] at bound
        linarith
    · simpa [realDigit] using excludes true false (by decide)

end LambdaCantor.Classical
