import LambdaCantor.ClassicalBridge
import LambdaCantor.Classical.Geometry
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
namespace LambdaCantor.Classical

/-- Four overlapping ordered intervals cover their complete corner interval. -/
theorem four_interval_cover (lower upper : Fin 4 → ℝ)
    (nonempty : ∀ i, lower i ≤ upper i)
    (overlap : ∀ i : Fin 3, lower ⟨i.val + 1, by omega⟩ ≤ upper ⟨i.val, by omega⟩)
    {target : ℝ} (bounds : lower 0 ≤ target ∧ target ≤ upper 3) :
    ∃ i, lower i ≤ target ∧ target ≤ upper i := by
  by_cases first : target ≤ upper 0
  · exact ⟨0, bounds.1, first⟩
  by_cases second : target ≤ upper 1
  · have adjacent : lower 1 ≤ upper 0 := by simpa using overlap 0
    exact ⟨1, by linarith, second⟩
  by_cases third : target ≤ upper 2
  · have adjacent : lower 2 ≤ upper 1 := by simpa using overlap 1
    exact ⟨2, by linarith, third⟩
  have adjacent : lower 3 ≤ upper 2 := by simpa using overlap 2
  exact ⟨3, by linarith, bounds.2⟩

/-- Passing exact finite-stage level intersections to the Cantor product. -/
theorem cantor_level_of_preCantor_levels (function : ℝ × ℝ → ℝ)
    (continuous : Continuous function) (target : ℝ)
    (finite_levels : ∀ n, ∃ point : ℝ × ℝ,
      point.1 ∈ preCantorSet n ∧ point.2 ∈ preCantorSet n ∧ function point = target) :
    ∃ point : ℝ × ℝ, point.1 ∈ _root_.cantorSet ∧
      point.2 ∈ _root_.cantorSet ∧ function point = target := by
  let levels : ℕ → Set (ℝ × ℝ) := fun n =>
    (preCantorSet n ×ˢ preCantorSet n) ∩ function ⁻¹' {target}
  have nested : ∀ n, levels (n + 1) ⊆ levels n := by
    intro n point membership
    exact ⟨⟨preCantorSet_antitone (by omega) membership.1.1,
      preCantorSet_antitone (by omega) membership.1.2⟩, membership.2⟩
  have nonempty : ∀ n, (levels n).Nonempty := by
    intro n
    obtain ⟨point, first, second, value⟩ := finite_levels n
    exact ⟨point, ⟨first, second⟩, value⟩
  have closed : ∀ n, IsClosed (levels n) := by
    intro n
    exact ((isClosed_preCantorSet n).prod (isClosed_preCantorSet n)).inter
      (isClosed_singleton.preimage continuous)
  have compact : IsCompact (levels 0) := by
    exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset (closed 0)
      (fun point membership => membership.1)
  obtain ⟨point, membership⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      levels nested nonempty compact closed
  have each : ∀ n, point ∈ levels n := Set.mem_iInter.mp membership
  exact ⟨point, Set.mem_iInter.mpr (fun n => (each n).1.1),
    Set.mem_iInter.mpr (fun n => (each n).1.2), (each 0).2⟩

/-- The three overlap inequalities for every square in the source unit square. -/
theorem cylinder_child_overlaps (u v side : ℝ)
    (u_nonnegative : 0 ≤ u) (v_nonnegative : 0 ≤ v)
    (side_nonnegative : 0 ≤ side) (u_upper : u + side ≤ 1) (v_upper : v + side ≤ 1) :
    cylinderPolynomial u (v + 2 * side / 3) ≤
      cylinderPolynomial (u + side / 3) (v + side / 3) ∧
    cylinderPolynomial (u + 2 * side / 3) v ≤
      cylinderPolynomial (u + side / 3) (v + side) ∧
    cylinderPolynomial (u + 2 * side / 3) (v + 2 * side / 3) ≤
      cylinderPolynomial (u + side) (v + side / 3) := by
  have side_upper : side ≤ 1 := by linarith
  have u_bound : u ≤ 1 := by linarith
  have v_bound : v ≤ 1 := by linarith
  have side_square : side ^ 2 ≤ side := by nlinarith
  have uside := mul_nonneg u_nonnegative side_nonnegative
  have vside := mul_nonneg v_nonnegative side_nonnegative
  have uside_upper := mul_le_mul_of_nonneg_right u_bound side_nonnegative
  have vside_upper := mul_le_mul_of_nonneg_right v_bound side_nonnegative
  unfold cylinderPolynomial
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem cylinder_children_cover (u v side target : ℝ)
    (u_nonnegative : 0 ≤ u) (v_nonnegative : 0 ≤ v)
    (side_nonnegative : 0 ≤ side) (u_upper : u + side ≤ 1) (v_upper : v + side ≤ 1)
    (lower : cylinderPolynomial u v ≤ target)
    (upper : target ≤ cylinderPolynomial (u + side) (v + side)) :
    ∃ first second : ℝ, (first = 0 ∨ first = 2) ∧ (second = 0 ∨ second = 2) ∧
      cylinderPolynomial (u + side * first / 3) (v + side * second / 3) ≤ target ∧
      target ≤ cylinderPolynomial (u + side * first / 3 + side / 3)
        (v + side * second / 3 + side / 3) := by
  obtain ⟨overlap_first, overlap_middle, overlap_last⟩ := cylinder_child_overlaps u v side
    u_nonnegative v_nonnegative side_nonnegative u_upper v_upper
  by_cases first : target ≤ cylinderPolynomial (u + side / 3) (v + side / 3)
  · refine ⟨0, 0, Or.inl rfl, Or.inl rfl, ?_, ?_⟩
    · simpa using lower
    · simpa using first
  by_cases second : target ≤ cylinderPolynomial (u + side / 3) (v + side)
  · refine ⟨0, 2, Or.inl rfl, Or.inr rfl, ?_, ?_⟩
    · simp only [mul_zero, zero_div, add_zero]
      simpa only [mul_comm side 2] using le_trans overlap_first (le_of_not_ge first)
    · convert second using 2 <;> ring
  by_cases third : target ≤ cylinderPolynomial (u + side) (v + side / 3)
  · refine ⟨2, 0, Or.inr rfl, Or.inl rfl, ?_, ?_⟩
    · simp only [mul_zero, zero_div, add_zero]
      simpa only [mul_comm side 2] using le_trans overlap_middle (le_of_not_ge second)
    · convert third using 2 <;> ring
  · refine ⟨2, 2, Or.inr rfl, Or.inr rfl, ?_, ?_⟩
    · simpa only [mul_comm side 2] using le_trans overlap_last (le_of_not_ge third)
    · convert upper using 2 <;> ring

theorem cylinder_preCantor_level (depth : ℕ) (u v side target : ℝ)
    (u_nonnegative : 0 ≤ u) (v_nonnegative : 0 ≤ v)
    (side_nonnegative : 0 ≤ side) (u_upper : u + side ≤ 1) (v_upper : v + side ≤ 1)
    (lower : cylinderPolynomial u v ≤ target)
    (upper : target ≤ cylinderPolynomial (u + side) (v + side)) :
    ∃ first second : ℝ, first ∈ preCantorSet depth ∧ second ∈ preCantorSet depth ∧
      cylinderPolynomial (u + side * first) (v + side * second) = target := by
  induction depth generalizing u v side with
  | zero =>
    have continuous_diagonal : Continuous (fun t : ℝ =>
        cylinderPolynomial (u + side * t) (v + side * t)) := by
      unfold cylinderPolynomial
      fun_prop
    have brackets : target ∈ Set.Icc
        (cylinderPolynomial (u + side * 0) (v + side * 0))
        (cylinderPolynomial (u + side * 1) (v + side * 1)) := by
      simpa using And.intro lower upper
    obtain ⟨parameter, membership, value⟩ :=
      intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
        continuous_diagonal.continuousOn brackets
    exact ⟨parameter, parameter, membership, membership, value⟩
  | succ depth inductionHypothesis =>
    obtain ⟨firstDigit, secondDigit, first_cases, second_cases, child_lower, child_upper⟩ :=
      cylinder_children_cover u v side target u_nonnegative v_nonnegative
        side_nonnegative u_upper v_upper lower upper
    have first_nonnegative : 0 ≤ u + side * firstDigit / 3 := by
      rcases first_cases with rfl | rfl <;> nlinarith
    have second_nonnegative : 0 ≤ v + side * secondDigit / 3 := by
      rcases second_cases with rfl | rfl <;> nlinarith
    have first_upper : u + side * firstDigit / 3 + side / 3 ≤ 1 := by
      rcases first_cases with rfl | rfl <;> nlinarith
    have second_upper : v + side * secondDigit / 3 + side / 3 ≤ 1 := by
      rcases second_cases with rfl | rfl <;> nlinarith
    obtain ⟨first, second, first_member, second_member, value⟩ :=
      inductionHypothesis (u + side * firstDigit / 3) (v + side * secondDigit / 3)
        (side / 3) first_nonnegative second_nonnegative (by positivity)
        first_upper second_upper child_lower child_upper
    refine ⟨(firstDigit + first) / 3, (secondDigit + second) / 3, ?_, ?_, ?_⟩
    · rcases first_cases with rfl | rfl
      · exact Or.inl ⟨first, first_member, by ring⟩
      · exact Or.inr ⟨first, first_member, rfl⟩
    · rcases second_cases with rfl | rfl
      · exact Or.inl ⟨second, second_member, by ring⟩
      · exact Or.inr ⟨second, second_member, rfl⟩
    · convert value using 1 <;> ring

/-- Actual Cantor-product crossing inside every square in the source rectangle. -/
theorem cylinder_cantor_level (u v side target : ℝ)
    (u_nonnegative : 0 ≤ u) (v_nonnegative : 0 ≤ v)
    (side_nonnegative : 0 ≤ side) (u_upper : u + side ≤ 1) (v_upper : v + side ≤ 1)
    (lower : cylinderPolynomial u v ≤ target)
    (upper : target ≤ cylinderPolynomial (u + side) (v + side)) :
    ∃ first second : ℝ, first ∈ _root_.cantorSet ∧ second ∈ _root_.cantorSet ∧
      cylinderPolynomial (u + side * first) (v + side * second) = target := by
  obtain ⟨point, first, second, value⟩ := cantor_level_of_preCantor_levels
    (fun point => cylinderPolynomial (u + side * point.1) (v + side * point.2))
    (by unfold cylinderPolynomial; fun_prop) target (fun depth => by
      obtain ⟨first, second, first_member, second_member, value⟩ :=
        cylinder_preCantor_level depth u v side target u_nonnegative v_nonnegative
          side_nonnegative u_upper v_upper lower upper
      exact ⟨(first, second), first_member, second_member, value⟩)
  exact ⟨point.1, point.2, first, second, value⟩

theorem source_level_nonempty :
    ∃ first second : ℝ, first ∈ LambdaCantor.cantorSet (1 / 3) ∧
      second ∈ LambdaCantor.cantorSet (1 / 3) ∧
      cylinderPolynomial first second = 3 ^ 16 := by
  obtain ⟨first, second, first_member, second_member, value⟩ :=
    cylinder_cantor_level 0 0 1 (3 ^ 16) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [cylinderPolynomial]) (by norm_num [cylinderPolynomial])
  refine ⟨first, second, ?_, ?_, ?_⟩
  · rw [cantorSet_third_eq]; exact first_member
  · rw [cantorSet_third_eq]; exact second_member
  · simpa using value

end LambdaCantor.Classical
