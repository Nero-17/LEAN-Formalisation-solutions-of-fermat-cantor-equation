import LambdaCantor.Classical.GeneralCover

noncomputable section
namespace LambdaCantor.Classical

def unitClamp (value : ℝ) : ℝ := max 0 (min 1 value)

theorem unitClamp_mem (value : ℝ) : unitClamp value ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem unitClamp_eq (value : ℝ) (membership : value ∈ Set.Icc (0 : ℝ) 1) :
    unitClamp value = value := by
  simp only [unitClamp, min_eq_right membership.2, max_eq_right membership.1]

theorem continuous_unitClamp : Continuous unitClamp := by
  unfold unitClamp
  fun_prop

theorem continuous_clamped (function : ℝ → ℝ → ℝ)
    (continuous : ContinuousOn (fun point : ℝ × ℝ => function point.1 point.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :
    Continuous (fun point : ℝ × ℝ => function (unitClamp point.1) (unitClamp point.2)) := by
  exact continuous.comp_continuous
    ((continuous_unitClamp.comp continuous_fst).prodMk (continuous_unitClamp.comp continuous_snd))
    (fun point => ⟨unitClamp_mem point.1, unitClamp_mem point.2⟩)

theorem coordinateBounds_clamped (function : ℝ → ℝ → ℝ)
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : CoordinateBounds function horizontalLower horizontalUpper verticalLower verticalUpper) :
    CoordinateBounds (fun x y => function (unitClamp x) (unitClamp y))
      horizontalLower horizontalUpper verticalLower verticalUpper := by
  constructor
  · intro y hy first hfirst second hsecond ordered
    simpa only [unitClamp_eq y hy, unitClamp_eq first hfirst, unitClamp_eq second hsecond]
      using bounds.horizontal y hy first hfirst second hsecond ordered
  · intro x hx first hfirst second hsecond ordered
    simpa only [unitClamp_eq x hx, unitClamp_eq first hfirst, unitClamp_eq second hsecond]
      using bounds.vertical x hx first hfirst second hsecond ordered

/-- Only continuity on the unit square is needed; clamping supplies an explicit
continuous extension, so no extension theorem is assumed as a black box. -/
theorem general_cantor_level_local (function : ℝ → ℝ → ℝ)
    (continuous : ContinuousOn (fun point : ℝ × ℝ => function point.1 point.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : CoordinateBounds function horizontalLower horizontalUpper verticalLower verticalUpper)
    (first_gap : verticalUpper ≤ horizontalLower)
    (middle_gap : horizontalUpper ≤ 3*verticalLower)
    (u v side target : ℝ) (u_nonnegative : 0 ≤ u) (v_nonnegative : 0 ≤ v)
    (side_nonnegative : 0 ≤ side) (u_upper : u+side ≤ 1) (v_upper : v+side ≤ 1)
    (lower : function u v ≤ target) (upper : target ≤ function (u+side) (v+side)) :
    ∃ first second : ℝ, first ∈ _root_.cantorSet ∧ second ∈ _root_.cantorSet ∧
      function (u+side*first) (v+side*second) = target := by
  have u_mem : u ∈ Set.Icc (0 : ℝ) 1 := ⟨u_nonnegative, by linarith⟩
  have v_mem : v ∈ Set.Icc (0 : ℝ) 1 := ⟨v_nonnegative, by linarith⟩
  have right_mem : u+side ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, u_upper⟩
  have top_mem : v+side ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, v_upper⟩
  obtain ⟨first, second, first_member, second_member, value⟩ := general_cantor_level
    (fun x y => function (unitClamp x) (unitClamp y)) (continuous_clamped function continuous)
    _ _ _ _ (coordinateBounds_clamped function _ _ _ _ bounds) first_gap middle_gap
    u v side target u_nonnegative v_nonnegative side_nonnegative u_upper v_upper
    (by simpa only [unitClamp_eq u u_mem, unitClamp_eq v v_mem] using lower)
    (by simpa only [unitClamp_eq (u+side) right_mem, unitClamp_eq (v+side) top_mem] using upper)
  have first_bounds := _root_.cantorSet_subset_unitInterval first_member
  have second_bounds := _root_.cantorSet_subset_unitInterval second_member
  have first_point : u+side*first ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [mul_nonneg side_nonnegative first_bounds.1,
      mul_le_mul_of_nonneg_left first_bounds.2 side_nonnegative]
  have second_point : v+side*second ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [mul_nonneg side_nonnegative second_bounds.1,
      mul_le_mul_of_nonneg_left second_bounds.2 side_nonnegative]
  refine ⟨first, second, first_member, second_member, ?_⟩
  simpa only [unitClamp_eq _ first_point, unitClamp_eq _ second_point] using value

theorem general_cantor_image (function : ℝ → ℝ → ℝ)
    (continuous : ContinuousOn (fun point : ℝ × ℝ => function point.1 point.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : CoordinateBounds function horizontalLower horizontalUpper verticalLower verticalUpper)
    (horizontal_nonnegative : 0 ≤ horizontalLower) (vertical_nonnegative : 0 ≤ verticalLower)
    (first_gap : verticalUpper ≤ horizontalLower)
    (middle_gap : horizontalUpper ≤ 3*verticalLower)
    (u v side : ℝ) (u_nonnegative : 0 ≤ u) (v_nonnegative : 0 ≤ v)
    (side_nonnegative : 0 ≤ side) (u_upper : u+side ≤ 1) (v_upper : v+side ≤ 1) :
    (fun point : ℝ × ℝ => function (u+side*point.1) (v+side*point.2)) ''
      (_root_.cantorSet ×ˢ _root_.cantorSet) =
        Set.Icc (function u v) (function (u+side) (v+side)) := by
  ext target
  constructor
  · rintro ⟨⟨first, second⟩, ⟨first_member, second_member⟩, rfl⟩
    have first_bounds := _root_.cantorSet_subset_unitInterval first_member
    have second_bounds := _root_.cantorSet_subset_unitInterval second_member
    have first_order : u ≤ u+side*first ∧ u+side*first ≤ u+side := by
      constructor <;> nlinarith [mul_nonneg side_nonnegative first_bounds.1,
        mul_le_mul_of_nonneg_left first_bounds.2 side_nonnegative]
    have second_order : v ≤ v+side*second ∧ v+side*second ≤ v+side := by
      constructor <;> nlinarith [mul_nonneg side_nonnegative second_bounds.1,
        mul_le_mul_of_nonneg_left second_bounds.2 side_nonnegative]
    have u_mem : u ∈ Set.Icc (0 : ℝ) 1 := ⟨u_nonnegative, by linarith⟩
    have v_mem : v ∈ Set.Icc (0 : ℝ) 1 := ⟨v_nonnegative, by linarith⟩
    have first_mem : u+side*first ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [first_order.1], by linarith [first_order.2]⟩
    have second_mem : v+side*second ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [second_order.1], by linarith [second_order.2]⟩
    have right_mem : u+side ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, u_upper⟩
    have top_mem : v+side ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, v_upper⟩
    have first_lower := (bounds.horizontal v v_mem u u_mem _ first_mem first_order.1).1
    have second_lower := (bounds.vertical _ first_mem v v_mem _ second_mem second_order.1).1
    have first_upper := (bounds.horizontal _ second_mem _ first_mem _ right_mem first_order.2).1
    have second_upper := (bounds.vertical _ right_mem _ second_mem _ top_mem second_order.2).1
    constructor
    · nlinarith [mul_nonneg horizontal_nonnegative (sub_nonneg.mpr first_order.1),
        mul_nonneg vertical_nonnegative (sub_nonneg.mpr second_order.1)]
    · nlinarith [mul_nonneg horizontal_nonnegative (sub_nonneg.mpr first_order.2),
        mul_nonneg vertical_nonnegative (sub_nonneg.mpr second_order.2)]
  · intro membership
    obtain ⟨first, second, first_member, second_member, value⟩ := general_cantor_level_local
      function continuous _ _ _ _ bounds first_gap middle_gap u v side target
      u_nonnegative v_nonnegative side_nonnegative u_upper v_upper membership.1 membership.2
    exact ⟨(first,second), ⟨first_member,second_member⟩, value⟩

end LambdaCantor.Classical
