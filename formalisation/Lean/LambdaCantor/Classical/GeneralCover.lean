import LambdaCantor.Classical.Cover
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
namespace LambdaCantor.Classical

/-- Coordinate increment estimates on the unit square. The mean-value theorem
below obtains these estimates from the partial-derivative hypotheses. -/
structure CoordinateBounds (function : ℝ → ℝ → ℝ)
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ) : Prop where
  horizontal : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ x₀ ∈ Set.Icc (0 : ℝ) 1,
    ∀ x₁ ∈ Set.Icc (0 : ℝ) 1, x₀ ≤ x₁ →
    horizontalLower * (x₁-x₀) ≤ function x₁ y - function x₀ y ∧
      function x₁ y - function x₀ y ≤ horizontalUpper * (x₁-x₀)
  vertical : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y₀ ∈ Set.Icc (0 : ℝ) 1,
    ∀ y₁ ∈ Set.Icc (0 : ℝ) 1, y₀ ≤ y₁ →
    verticalLower * (y₁-y₀) ≤ function x y₁ - function x y₀ ∧
      function x y₁ - function x y₀ ≤ verticalUpper * (y₁-y₀)

theorem increment_bounds_of_deriv (function : ℝ → ℝ) (lower upper : ℝ)
    (continuous : ContinuousOn function (Set.Icc (0 : ℝ) 1))
    (differentiable : DifferentiableOn ℝ function (Set.Ioo (0 : ℝ) 1))
    (bounds : ∀ x ∈ Set.Ioo (0 : ℝ) 1, lower ≤ deriv function x ∧ deriv function x ≤ upper)
    (first second : ℝ) (first_mem : first ∈ Set.Icc (0 : ℝ) 1)
    (second_mem : second ∈ Set.Icc (0 : ℝ) 1) (ordered : first ≤ second) :
    lower * (second-first) ≤ function second - function first ∧
      function second - function first ≤ upper * (second-first) := by
  have differentiable' : DifferentiableOn ℝ function (interior (Set.Icc (0 : ℝ) 1)) := by
    simpa only [interior_Icc] using differentiable
  constructor
  · apply (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv continuous differentiable'
      (fun x hx => (bounds x (by simpa only [interior_Icc] using hx)).1)
      first first_mem second second_mem ordered
  · apply (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le continuous differentiable'
      (fun x hx => (bounds x (by simpa only [interior_Icc] using hx)).2)
      first first_mem second second_mem ordered

theorem coordinateBounds_of_partial_derivatives
    (function : ℝ → ℝ → ℝ)
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (horizontal_continuous : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ContinuousOn (fun x => function x y) (Set.Icc (0 : ℝ) 1))
    (vertical_continuous : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ContinuousOn (fun y => function x y) (Set.Icc (0 : ℝ) 1))
    (horizontal_differentiable : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableOn ℝ (fun x => function x y) (Set.Ioo (0 : ℝ) 1))
    (vertical_differentiable : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableOn ℝ (fun y => function x y) (Set.Ioo (0 : ℝ) 1))
    (horizontal_bounds : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      horizontalLower ≤ deriv (fun t => function t y) x ∧
        deriv (fun t => function t y) x ≤ horizontalUpper)
    (vertical_bounds : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      verticalLower ≤ deriv (fun t => function x t) y ∧
        deriv (fun t => function x t) y ≤ verticalUpper) :
    CoordinateBounds function horizontalLower horizontalUpper verticalLower verticalUpper := by
  constructor
  · intro y hy first hfirst second hsecond ordered
    exact increment_bounds_of_deriv _ _ _ (horizontal_continuous y hy)
      (horizontal_differentiable y hy) (horizontal_bounds y hy) first second hfirst hsecond ordered
  · intro x hx first hfirst second hsecond ordered
    exact increment_bounds_of_deriv _ _ _ (vertical_continuous x hx)
      (vertical_differentiable x hx) (vertical_bounds x hx) first second hfirst hsecond ordered

theorem general_child_overlaps (function : ℝ → ℝ → ℝ)
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : CoordinateBounds function horizontalLower horizontalUpper verticalLower verticalUpper)
    (first_gap : verticalUpper ≤ horizontalLower)
    (middle_gap : horizontalUpper ≤ 3 * verticalLower)
    (u v side : ℝ) (u_nonnegative : 0 ≤ u) (v_nonnegative : 0 ≤ v)
    (side_nonnegative : 0 ≤ side) (u_upper : u+side ≤ 1) (v_upper : v+side ≤ 1) :
    function u (v+2*side/3) ≤ function (u+side/3) (v+side/3) ∧
    function (u+2*side/3) v ≤ function (u+side/3) (v+side) ∧
    function (u+2*side/3) (v+2*side/3) ≤ function (u+side) (v+side/3) := by
  have horizontal_first := (bounds.horizontal (v+side/3) ⟨by linarith, by linarith⟩
    u ⟨u_nonnegative, by linarith⟩ (u+side/3) ⟨by linarith, by linarith⟩ (by linarith)).1
  have vertical_first := (bounds.vertical u ⟨u_nonnegative, by linarith⟩
    (v+side/3) ⟨by linarith, by linarith⟩ (v+2*side/3) ⟨by linarith, by linarith⟩
    (by linarith)).2
  have horizontal_middle := (bounds.horizontal v ⟨v_nonnegative, by linarith⟩
    (u+side/3) ⟨by linarith, by linarith⟩ (u+2*side/3) ⟨by linarith, by linarith⟩
    (by linarith)).2
  have vertical_middle := (bounds.vertical (u+side/3) ⟨by linarith, by linarith⟩
    v ⟨v_nonnegative, by linarith⟩ (v+side) ⟨by linarith, v_upper⟩ (by linarith)).1
  have horizontal_last := (bounds.horizontal (v+side/3) ⟨by linarith, by linarith⟩
    (u+2*side/3) ⟨by linarith, by linarith⟩ (u+side) ⟨by linarith, u_upper⟩
    (by linarith)).1
  have vertical_last := (bounds.vertical (u+2*side/3) ⟨by linarith, by linarith⟩
    (v+side/3) ⟨by linarith, by linarith⟩ (v+2*side/3) ⟨by linarith, by linarith⟩
    (by linarith)).2
  have first_margin := mul_nonneg side_nonnegative (sub_nonneg.mpr first_gap)
  have middle_margin := mul_nonneg side_nonnegative (sub_nonneg.mpr middle_gap)
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem general_children_cover (function : ℝ → ℝ → ℝ)
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : CoordinateBounds function horizontalLower horizontalUpper verticalLower verticalUpper)
    (first_gap : verticalUpper ≤ horizontalLower)
    (middle_gap : horizontalUpper ≤ 3 * verticalLower)
    (u v side target : ℝ) (u_nonnegative : 0 ≤ u) (v_nonnegative : 0 ≤ v)
    (side_nonnegative : 0 ≤ side) (u_upper : u+side ≤ 1) (v_upper : v+side ≤ 1)
    (lower : function u v ≤ target) (upper : target ≤ function (u+side) (v+side)) :
    ∃ firstDigit secondDigit : ℝ, (firstDigit=0 ∨ firstDigit=2) ∧
      (secondDigit=0 ∨ secondDigit=2) ∧
      function (u+side*firstDigit/3) (v+side*secondDigit/3) ≤ target ∧
      target ≤ function (u+side*firstDigit/3+side/3) (v+side*secondDigit/3+side/3) := by
  have overlaps := general_child_overlaps function _ _ _ _ bounds first_gap middle_gap
    u v side u_nonnegative v_nonnegative side_nonnegative u_upper v_upper
  by_cases first : target ≤ function (u+side/3) (v+side/3)
  · exact ⟨0, 0, Or.inl rfl, Or.inl rfl, by simpa using lower, by simpa using first⟩
  by_cases second : target ≤ function (u+side/3) (v+side)
  · refine ⟨0, 2, Or.inl rfl, Or.inr rfl, ?_, ?_⟩
    · simpa [mul_comm side 2] using overlaps.1.trans (le_of_not_ge first)
    · convert second using 1 <;> congr 1 <;> ring
  by_cases third : target ≤ function (u+side) (v+side/3)
  · refine ⟨2, 0, Or.inr rfl, Or.inl rfl, ?_, ?_⟩
    · simpa [mul_comm side 2] using overlaps.2.1.trans (le_of_not_ge second)
    · convert third using 1 <;> congr 1 <;> ring
  refine ⟨2, 2, Or.inr rfl, Or.inr rfl, ?_, ?_⟩
  · simpa [mul_comm side 2] using overlaps.2.2.trans (le_of_not_ge third)
  · convert upper using 1 <;> congr 1 <;> ring

theorem general_preCantor_level (function : ℝ → ℝ → ℝ)
    (continuous : Continuous (fun point : ℝ × ℝ => function point.1 point.2))
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : CoordinateBounds function horizontalLower horizontalUpper verticalLower verticalUpper)
    (first_gap : verticalUpper ≤ horizontalLower)
    (middle_gap : horizontalUpper ≤ 3 * verticalLower)
    (depth : ℕ) (u v side target : ℝ)
    (u_nonnegative : 0 ≤ u) (v_nonnegative : 0 ≤ v) (side_nonnegative : 0 ≤ side)
    (u_upper : u+side ≤ 1) (v_upper : v+side ≤ 1)
    (lower : function u v ≤ target) (upper : target ≤ function (u+side) (v+side)) :
    ∃ first second : ℝ, first ∈ preCantorSet depth ∧ second ∈ preCantorSet depth ∧
      function (u+side*first) (v+side*second) = target := by
  induction depth generalizing u v side with
  | zero =>
    have continuous_map : Continuous (fun t : ℝ => (u+side*t, v+side*t)) := by fun_prop
    have diagonal : Continuous (fun t : ℝ => function (u+side*t) (v+side*t)) :=
      continuous.comp continuous_map
    have brackets : target ∈ Set.Icc (function (u+side*0) (v+side*0))
        (function (u+side*1) (v+side*1)) := by simpa using And.intro lower upper
    obtain ⟨parameter, membership, value⟩ := intermediate_value_Icc
      (by norm_num : (0 : ℝ) ≤ 1) diagonal.continuousOn brackets
    exact ⟨parameter, parameter, membership, membership, value⟩
  | succ depth inductionHypothesis =>
    obtain ⟨firstDigit, secondDigit, first_cases, second_cases, child_lower, child_upper⟩ :=
      general_children_cover function _ _ _ _ bounds first_gap middle_gap u v side target
        u_nonnegative v_nonnegative side_nonnegative u_upper v_upper lower upper
    have first_nonnegative : 0 ≤ u+side*firstDigit/3 := by
      rcases first_cases with rfl | rfl <;> nlinarith
    have second_nonnegative : 0 ≤ v+side*secondDigit/3 := by
      rcases second_cases with rfl | rfl <;> nlinarith
    have first_upper : u+side*firstDigit/3+side/3 ≤ 1 := by
      rcases first_cases with rfl | rfl <;> nlinarith
    have second_upper : v+side*secondDigit/3+side/3 ≤ 1 := by
      rcases second_cases with rfl | rfl <;> nlinarith
    obtain ⟨first, second, first_member, second_member, value⟩ := inductionHypothesis
      (u+side*firstDigit/3) (v+side*secondDigit/3) (side/3)
      first_nonnegative second_nonnegative (by positivity) first_upper second_upper child_lower child_upper
    refine ⟨(firstDigit+first)/3, (secondDigit+second)/3, ?_, ?_, ?_⟩
    · rcases first_cases with rfl | rfl
      · exact Or.inl ⟨first, first_member, by ring⟩
      · exact Or.inr ⟨first, first_member, rfl⟩
    · rcases second_cases with rfl | rfl
      · exact Or.inl ⟨second, second_member, by ring⟩
      · exact Or.inr ⟨second, second_member, rfl⟩
    · convert value using 1 <;> ring

/-- General Cantor crossing criterion inside every descendant square. -/
theorem general_cantor_level (function : ℝ → ℝ → ℝ)
    (continuous : Continuous (fun point : ℝ × ℝ => function point.1 point.2))
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : CoordinateBounds function horizontalLower horizontalUpper verticalLower verticalUpper)
    (first_gap : verticalUpper ≤ horizontalLower)
    (middle_gap : horizontalUpper ≤ 3 * verticalLower)
    (u v side target : ℝ) (u_nonnegative : 0 ≤ u) (v_nonnegative : 0 ≤ v)
    (side_nonnegative : 0 ≤ side) (u_upper : u+side ≤ 1) (v_upper : v+side ≤ 1)
    (lower : function u v ≤ target) (upper : target ≤ function (u+side) (v+side)) :
    ∃ first second : ℝ, first ∈ _root_.cantorSet ∧ second ∈ _root_.cantorSet ∧
      function (u+side*first) (v+side*second) = target := by
  have continuous_map : Continuous (fun point : ℝ × ℝ =>
      (u+side*point.1, v+side*point.2)) := by fun_prop
  obtain ⟨point, first, second, value⟩ := cantor_level_of_preCantor_levels
    (fun point => function (u+side*point.1) (v+side*point.2))
    (continuous.comp continuous_map) target (fun depth => by
      obtain ⟨first, second, first_member, second_member, value⟩ :=
        general_preCantor_level function continuous _ _ _ _ bounds first_gap middle_gap
          depth u v side target u_nonnegative v_nonnegative side_nonnegative u_upper v_upper lower upper
      exact ⟨(first,second), first_member, second_member, value⟩)
  exact ⟨point.1, point.2, first, second, value⟩

end LambdaCantor.Classical
