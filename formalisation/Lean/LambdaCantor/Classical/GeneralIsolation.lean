import LambdaCantor.Classical.LocalUniqueness
import LambdaCantor.Classical.GeneralCoverLocal

noncomputable section
namespace LambdaCantor.Classical

/-- Local analytic data for a shrinking retained square. The crossing clause is
provided by the general cover theorem; the normalized error comes from differentiability. -/
structure SquareApproximation (function : ℝ → ℝ → ℝ)
    (u v a b tailA tailB side slope error : ℝ) : Prop where
  error_nonnegative : 0 ≤ error
  crossing : ∀ x y size target : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ size →
    x + size ≤ 1 → y + size ≤ 1 → function x y ≤ target →
    target ≤ function (x + size) (y + size) →
    ∃ first second : ℝ, first ∈ _root_.cantorSet ∧ second ∈ _root_.cantorSet ∧
      function (x + size * first) (y + size * second) = target
  normalized : ∃ scale : ℝ, 0 < scale ∧ ∀ x y : ℝ,
    x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
    |(function (a + side * (x - tailA)) (b + side * (y - tailB)) - function a b) / scale -
      ((slope * x + y) / 2 - (slope * tailA + tailB) / 2)| ≤ error

theorem squareApproximation_of_coordinateBounds (function : ℝ → ℝ → ℝ)
    (continuous : ContinuousOn (fun point : ℝ × ℝ => function point.1 point.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : CoordinateBounds function horizontalLower horizontalUpper verticalLower verticalUpper)
    (first_gap : verticalUpper ≤ horizontalLower)
    (middle_gap : horizontalUpper ≤ 3 * verticalLower)
    (u v a b tailA tailB side slope error scale : ℝ)
    (error_nonnegative : 0 ≤ error) (scale_positive : 0 < scale)
    (estimate : ∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      |(function (a + side * (x - tailA)) (b + side * (y - tailB)) - function a b) / scale -
        ((slope * x + y) / 2 - (slope * tailA + tailB) / 2)| ≤ error) :
    SquareApproximation function u v a b tailA tailB side slope error := by
  refine ⟨error_nonnegative, ?_, ⟨scale, scale_positive, estimate⟩⟩
  intro x y size target x_nonnegative y_nonnegative size_nonnegative x_upper y_upper lower upper
  exact general_cantor_level_local function continuous _ _ _ _ bounds first_gap middle_gap
    x y size target x_nonnegative y_nonnegative size_nonnegative x_upper y_upper lower upper

theorem SquareApproximation.brackets {function : ℝ → ℝ → ℝ}
    {u v a b tailA tailB side slope error : ℝ}
    (model : SquareApproximation function u v a b tailA tailB side slope error)
    (first second : Bool)
    (lower : realDigit slope first second / 3 + error < (slope * tailA + tailB) / 2)
    (upper : (slope * tailA + tailB) / 2 <
      realDigit slope first second / 3 + (slope + 1) / 6 - error) :
    function (a + side * (ternaryChild first 0 - tailA))
      (b + side * (ternaryChild second 0 - tailB)) < function a b ∧
    function a b < function (a + side * (ternaryChild first 1 - tailA))
      (b + side * (ternaryChild second 1 - tailB)) := by
  obtain ⟨scale, positive, estimate⟩ := model.normalized
  have lower_error := abs_le.mp (estimate (ternaryChild first 0) (ternaryChild second 0)
    (ternaryChild_bounds first (by norm_num)) (ternaryChild_bounds second (by norm_num)))
  have upper_error := abs_le.mp (estimate (ternaryChild first 1) (ternaryChild second 1)
    (ternaryChild_bounds first (by norm_num)) (ternaryChild_bounds second (by norm_num)))
  have corners := child_linear_corners slope first second
  rw [corners.1] at lower_error
  rw [corners.2] at upper_error
  constructor
  · have negative : (function (a + side * (ternaryChild first 0 - tailA))
        (b + side * (ternaryChild second 0 - tailB)) - function a b) / scale < 0 := by
      linarith [lower_error.2]
    have numerator := (div_lt_iff₀ positive).mp negative
    linarith
  · have greater : 0 < (function (a + side * (ternaryChild first 1 - tailA))
        (b + side * (ternaryChild second 1 - tailB)) - function a b) / scale := by
      linarith [upper_error.1]
    have numerator := (lt_div_iff₀ positive).mp greater
    linarith

theorem general_trimmed_child_level (function : ℝ → ℝ → ℝ) (slope error : ℝ)
    (u v a b tailA tailB side : ℝ)
    (model : SquareApproximation function u v a b tailA tailB side slope error) (first second : Bool)
    (u_nonnegative : 0 ≤ u) (v_nonnegative : 0 ≤ v)
    (side_positive : 0 < side) (u_upper : u + side ≤ 1) (v_upper : v + side ≤ 1)
    (tailA_bounds : tailA ∈ Set.Icc (0 : ℝ) 1)
    (tailB_bounds : tailB ∈ Set.Icc (0 : ℝ) 1)
    (first_decomposition : a = u + side * tailA)
    (second_decomposition : b = v + side * tailB)
    (lower : realDigit slope first second / 3 +
        error < (slope * tailA + tailB) / 2)
    (upper : (slope * tailA + tailB) / 2 <
        realDigit slope first second / 3 +
          (slope + 1) / 6 - error) :
    ∃ nextA nextB : ℝ, nextA ∈ cantorSet (1 / 3) ∧ nextB ∈ cantorSet (1 / 3) ∧
      function (u + side * ternaryChild first nextA)
        (v + side * ternaryChild second nextB) = function a b := by
  have brackets := model.brackets first second lower upper
  have child_u_nonnegative : 0 ≤ u + side * ternaryChild first 0 := by
    cases first <;> simp [ternaryChild] <;> nlinarith
  have child_v_nonnegative : 0 ≤ v + side * ternaryChild second 0 := by
    cases second <;> simp [ternaryChild] <;> nlinarith
  have child_u_upper : u + side * ternaryChild first 0 + side / 3 ≤ 1 := by
    cases first <;> simp [ternaryChild] <;> nlinarith
  have child_v_upper : v + side * ternaryChild second 0 + side / 3 ≤ 1 := by
    cases second <;> simp [ternaryChild] <;> nlinarith
  have child_lower : function (u + side * ternaryChild first 0)
      (v + side * ternaryChild second 0) ≤ function a b := by
    have first_coordinate : a + side * (ternaryChild first 0 - tailA) =
        u + side * ternaryChild first 0 := by rw [first_decomposition]; ring
    have second_coordinate : b + side * (ternaryChild second 0 - tailB) =
        v + side * ternaryChild second 0 := by rw [second_decomposition]; ring
    simpa only [first_coordinate, second_coordinate] using brackets.1.le
  have child_upper : function a b ≤
      function (u + side * ternaryChild first 0 + side / 3)
        (v + side * ternaryChild second 0 + side / 3) := by
    have first_coordinate : a + side * (ternaryChild first 1 - tailA) =
        u + side * ternaryChild first 0 + side / 3 := by
      rw [first_decomposition]; unfold ternaryChild; ring
    have second_coordinate : b + side * (ternaryChild second 1 - tailB) =
        v + side * ternaryChild second 0 + side / 3 := by
      rw [second_decomposition]; unfold ternaryChild; ring
    simpa only [first_coordinate, second_coordinate] using brackets.2.le
  obtain ⟨nextA, nextB, first_member, second_member, value⟩ :=
    model.crossing (u + side * ternaryChild first 0)
      (v + side * ternaryChild second 0) (side / 3) (function a b)
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

theorem general_unique_square_forces_label (function : ℝ → ℝ → ℝ) (slope error : ℝ)
    (u v a b tailA tailB side : ℝ)
    (model : SquareApproximation function u v a b tailA tailB side slope error)
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
      function (u + side * first) (v + side * second) = function a b →
        u + side * first = a ∧ v + side * second = b)
    (lower : realDigit slope competingFirst competingSecond / 3 +
        error < (slope * tailA + tailB) / 2)
    (upper : (slope * tailA + tailB) / 2 <
        realDigit slope competingFirst competingSecond / 3 +
          (slope + 1) / 6 - error) :
    originalFirst = competingFirst ∧ originalSecond = competingSecond := by
  obtain ⟨nextA, nextB, first_member, second_member, value⟩ :=
    general_trimmed_child_level function slope error u v a b tailA tailB side model competingFirst competingSecond
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

/-- The endpoint-safe exclusive-domain estimate derived from actual uniqueness. -/
theorem general_unique_square_exclusive (function : ℝ → ℝ → ℝ) (slope error : ℝ)
    (u v a b tailA tailB side : ℝ)
    (model : SquareApproximation function u v a b tailA tailB side slope error)
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
      function (u + side * first) (v + side * second) = function a b →
        u + side * first = a ∧ v + side * second = b)
    (slope_nonnegative : 0 ≤ slope)
    (small_error : error < 1 / 3)
    (small_gap : error < (slope - 1) / 3) :
    exclusiveLower slope originalFirst originalSecond -
        error ≤ (slope * tailA + tailB) / 2 ∧
    (slope * tailA + tailB) / 2 ≤
      exclusiveUpper slope originalFirst originalSecond +
        error := by
  have own_bounds := linear_child_bounds slope
    originalFirst originalSecond originalNextA originalNextB slope_nonnegative
    nextA_bounds nextB_bounds
  rw [← first_tail, ← second_tail] at own_bounds
  have excludes (competingFirst competingSecond : Bool)
      (different : (originalFirst, originalSecond) ≠ (competingFirst, competingSecond)) :
      ¬ (realDigit slope competingFirst competingSecond / 3 +
          error < (slope * tailA + tailB) / 2 ∧
        (slope * tailA + tailB) / 2 <
          realDigit slope competingFirst competingSecond / 3 +
            (slope + 1) / 6 - error) := by
    rintro ⟨lower, upper⟩
    have equal_labels := general_unique_square_forces_label function slope error u v a b tailA tailB side model
      originalFirst originalSecond competingFirst competingSecond originalNextA originalNextB
      u_nonnegative v_nonnegative side_positive u_upper v_upper tailA_bounds tailB_bounds
      nextA_bounds nextB_bounds first_tail second_tail first_decomposition second_decomposition
      unique lower upper
    exact different (Prod.ext equal_labels.1 equal_labels.2)
  have error_nonnegative : 0 ≤ error := model.error_nonnegative
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
