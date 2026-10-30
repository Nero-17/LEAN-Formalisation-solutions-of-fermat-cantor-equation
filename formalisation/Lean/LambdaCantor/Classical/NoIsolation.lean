import LambdaCantor.Classical.Isolation
import LambdaCantor.Classical.PeriodicityConclusion
import LambdaCantor.Classical.Rational
import LambdaCantor.Classical.RationalAddress
import LambdaCantor.PerfectCardinality

noncomputable section
namespace LambdaCantor.Classical

def digitLabel (first second : Bool) : Fin 4 :=
  ⟨(if first then 2 else 0) + (if second then 1 else 0), by
    cases first <;> cases second <;> decide⟩

theorem digitLabel_injective {first second otherFirst otherSecond : Bool}
    (equality : digitLabel first second = digitLabel otherFirst otherSecond) :
    first = otherFirst ∧ second = otherSecond := by
  have values := congrArg Fin.val equality
  cases first <;> cases second <;> cases otherFirst <;> cases otherSecond <;>
    simp_all [digitLabel]

def linearTail (slope : ℝ) (first second : ℕ → Bool) (depth : ℕ) : ℝ :=
  (slope * tailAddress first depth + tailAddress second depth) / 2

theorem linearTail_recurrence (slope : ℝ) (first second : ℕ → Bool) (depth : ℕ) :
    linearTail slope first second (depth + 1) = 3 * linearTail slope first second depth -
      (((digitLabel (first depth) (second depth)).val / 2 : ℕ) : ℝ) * slope -
      (((digitLabel (first depth) (second depth)).val % 2 : ℕ) : ℝ) := by
  unfold linearTail
  rw [tailAddress_step first depth, tailAddress_step second depth]
  cases first_value : first depth <;> cases second_value : second depth <;>
    simp [digitLabel, ternaryChild, first_value, second_value] <;> ring

theorem exclusiveLower_coefficient (slope : ℝ) (first second : Bool) :
    exclusiveLower slope first second =
      ((Integer.lowerCoefficient (digitLabel first second).val).1 * slope +
        (Integer.lowerCoefficient (digitLabel first second).val).2) / 6 := by
  cases first <;> cases second <;>
    norm_num [digitLabel, exclusiveLower, Integer.lowerCoefficient]

theorem exclusiveUpper_coefficient (slope : ℝ) (first second : Bool) :
    exclusiveUpper slope first second =
      ((Integer.upperCoefficient (digitLabel first second).val).1 * slope +
        (Integer.upperCoefficient (digitLabel first second).val).2) / 6 := by
  cases first <;> cases second <;>
    norm_num [digitLabel, exclusiveUpper, Integer.upperCoefficient] <;> ring

theorem isolated_level_addresses_periodic (first second : ℕ → Bool)
    (level : cylinderPolynomial (address (1 / 3) first) (address (1 / 3) second) = 3 ^ 16)
    (radius : ℝ) (radius_positive : 0 < radius)
    (isolated : ∀ point ∈ sourceLevel,
      dist point (address (1 / 3) first, address (1 / 3) second) < radius →
        point = (address (1 / 3) first, address (1 / 3) second)) :
    ∃ start, ∀ depth ≥ start, first (depth + 4) = first depth ∧ second (depth + 4) = second depth := by
  obtain ⟨beginning, exclusive⟩ := isolated_level_eventually_exclusive first second
    level radius radius_positive isolated
  have first_bounds : address (1 / 3) first ∈ Set.Icc (0 : ℝ) 1 :=
    LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) ⟨_, rfl⟩
  have second_bounds : address (1 / 3) second ∈ Set.Icc (0 : ℝ) 1 :=
    LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) ⟨_, rfl⟩
  have slope_bounds := cylinder_ratio_bounds _ _ first_bounds second_bounds
  obtain ⟨periodStart, periodic⟩ := exclusive_domains_eventually_periodic
    ((6336 + address (1 / 3) first) / (9 * (566 + address (1 / 3) second)))
    slope_bounds.1 slope_bounds.2
    (fun n => digitLabel (first (n + beginning)) (second (n + beginning)))
    (fun n => linearTail ((6336 + address (1 / 3) first) /
      (9 * (566 + address (1 / 3) second))) first second (n + beginning))
    (fun n => curvatureError (n + beginning))
    (fun n => curvatureError_nonnegative (n + beginning))
    (fun error positive => by
      obtain ⟨start, bound⟩ := curvatureError_vanishes error positive
      exact ⟨start, fun n large => bound (n + beginning) (by omega)⟩)
    (fun n => by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      linearTail_recurrence ((6336 + address (1 / 3) first) /
        (9 * (566 + address (1 / 3) second))) first second (n + beginning))
    (fun n => by
      rw [← exclusiveLower_coefficient]
      exact (exclusive (n + beginning) (by omega)).1)
    (fun n => by
      rw [← exclusiveUpper_coefficient]
      exact (exclusive (n + beginning) (by omega)).2)
  refine ⟨beginning + periodStart, fun depth large => ?_⟩
  have labels := periodic (depth - beginning) (by omega)
  have first_index : depth - beginning + 4 + beginning = depth + 4 := by omega
  have second_index : depth - beginning + beginning = depth := by omega
  simp only [first_index, second_index] at labels
  exact digitLabel_injective labels

theorem isolated_level_impossible (first second : ℕ → Bool)
    (level : cylinderPolynomial (address (1 / 3) first) (address (1 / 3) second) = 3 ^ 16)
    (radius : ℝ) (radius_positive : 0 < radius)
    (isolated : ∀ point ∈ sourceLevel,
      dist point (address (1 / 3) first, address (1 / 3) second) < radius →
        point = (address (1 / 3) first, address (1 / 3) second)) : False := by
  obtain ⟨start, periodic⟩ := isolated_level_addresses_periodic first second
    level radius radius_positive isolated
  have first_rational := rational_address_of_eventually_periodic first
    ⟨start, 4, by omega, fun n large => (periodic n large).1⟩
  have second_rational := rational_address_of_eventually_periodic second
    ⟨start, 4, by omega, fun n large => (periodic n large).2⟩
  obtain ⟨x, x_represents⟩ := rational_affine_cylinder 566 7 _ second_rational
  obtain ⟨y, y_represents⟩ := rational_affine_cylinder 6336 8 _ first_rational
  simp only [Nat.cast_ofNat] at x_represents y_represents
  have first_bounds : address (1 / 3) first ∈ Set.Icc (0 : ℝ) 1 :=
    LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) ⟨_, rfl⟩
  have second_bounds : address (1 / 3) second ∈ Set.Icc (0 : ℝ) 1 :=
    LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) ⟨_, rfl⟩
  have interior := cylinder_coordinates_interior _ _ first_bounds second_bounds
  rw [← x_represents, ← y_represents] at interior
  apply no_rational_interior_circle x y
    (by exact_mod_cast interior.1.1) (by exact_mod_cast interior.1.2)
    (by exact_mod_cast interior.2.1) (by exact_mod_cast interior.2.2)
  · rw [x_represents]
    exact source_x_mem_cantor ⟨second, rfl⟩
  · rw [y_represents]
    exact source_y_mem_cantor ⟨first, rfl⟩
  · rw [x_represents, y_represents]
    exact (cylinder_circle_iff _ _).mpr level

theorem sourceLevel_no_isolated (point : ℝ × ℝ) (membership : point ∈ sourceLevel)
    (radius : ℝ) (radius_positive : 0 < radius) :
    ¬ (∀ other ∈ sourceLevel, dist other point < radius → other = point) := by
  rcases point with ⟨a, b⟩
  obtain ⟨first, first_value⟩ := membership.1.1
  obtain ⟨second, second_value⟩ := membership.1.2
  have level : cylinderPolynomial (address (1 / 3) first) (address (1 / 3) second) = 3 ^ 16 := by
    rw [first_value, second_value]
    exact membership.2
  intro isolated
  apply isolated_level_impossible first second level radius radius_positive
  simpa only [first_value, second_value] using isolated

theorem sourceLevel_perfect : Perfect sourceLevel := by
  refine ⟨sourceLevel_compact.isClosed, ?_⟩
  rw [preperfect_iff_nhds]
  intro point membership neighborhood neighborhood_member
  obtain ⟨radius, positive, ball_contained⟩ := Metric.mem_nhds_iff.mp neighborhood_member
  by_contra absence
  push_neg at absence
  apply sourceLevel_no_isolated point membership radius positive
  intro other other_member nearby
  exact absence other ⟨ball_contained nearby, other_member⟩

theorem cylinderMap_dist_le (first second : ℝ × ℝ) :
    dist (cylinderMap first) (cylinderMap second) ≤ dist first second := by
  have first_bound : dist first.1 second.1 ≤ dist first second := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have second_bound : dist first.2 second.2 ≤ dist first second := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have first_distance : dist ((566 + first.2) / 3 ^ 7) ((566 + second.2) / 3 ^ 7) =
      dist first.2 second.2 / 3 ^ 7 := by
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, add_sub_add_left_eq_sub, abs_div]
    norm_num
  have second_distance : dist ((6336 + first.1) / 3 ^ 8) ((6336 + second.1) / 3 ^ 8) =
      dist first.1 second.1 / 3 ^ 8 := by
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, add_sub_add_left_eq_sub, abs_div]
    norm_num
  unfold cylinderMap
  rw [Prod.dist_eq, first_distance, second_distance]
  apply max_le
  · have nonnegative : 0 ≤ dist first.2 second.2 := dist_nonneg
    norm_num
    nlinarith
  · have nonnegative : 0 ≤ dist first.1 second.1 := dist_nonneg
    norm_num
    nlinarith

theorem source_no_isolated (point : ℝ × ℝ) (membership : point ∈ source)
    (radius : ℝ) (radius_positive : 0 < radius) :
    ¬ (∀ other ∈ source, dist other point < radius → other = point) := by
  obtain ⟨preimage, preimage_member, rfl⟩ := membership
  intro isolated
  apply sourceLevel_no_isolated preimage preimage_member radius radius_positive
  intro other other_member nearby
  apply cylinderMap_injective
  exact isolated (cylinderMap other) ⟨other, other_member, rfl⟩
    (lt_of_le_of_lt (cylinderMap_dist_le other preimage) nearby)

theorem source_perfect : Perfect source := by
  refine ⟨source_compact.isClosed, ?_⟩
  rw [preperfect_iff_nhds]
  intro point membership neighborhood neighborhood_member
  obtain ⟨radius, positive, ball_contained⟩ := Metric.mem_nhds_iff.mp neighborhood_member
  by_contra absence
  push_neg at absence
  apply source_no_isolated point membership radius positive
  intro other other_member nearby
  exact absence other ⟨ball_contained nearby, other_member⟩

/-- The cardinality conclusion of the classical-circle construction. -/
theorem classical_circle_cardinality :
    Cardinal.mk (intersection 2 (1 / 3)) = Cardinal.continuum := by
  have source_cardinality := cardinal_eq_continuum_of_perfect_subset sourceLevel_perfect
    sourceLevel_nonempty (Set.Subset.refl sourceLevel)
  have lower : Cardinal.mk sourceLevel ≤ Cardinal.mk (intersection 2 (1 / 3)) := by
    apply Cardinal.mk_le_of_injective (f := fun point : sourceLevel =>
      (⟨cylinderMap point.val, source_subset_circle ⟨point.val, point.property, rfl⟩⟩ :
        intersection 2 (1 / 3)))
    intro first second equality
    apply Subtype.ext
    exact cylinderMap_injective (congrArg Subtype.val equality)
  rw [source_cardinality] at lower
  have upper := Cardinal.mk_set_le (intersection 2 (1 / 3))
  have plane : Cardinal.mk (ℝ × ℝ) = Cardinal.continuum := by
    simp [Cardinal.mk_prod, Cardinal.mk_real, Cardinal.continuum_mul_self]
  rw [plane] at upper
  exact le_antisymm upper lower

end LambdaCantor.Classical
