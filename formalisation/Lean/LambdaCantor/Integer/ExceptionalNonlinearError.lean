import LambdaCantor.Integer.ExceptionalSource
import LambdaCantor.Integer.PowerRemainder
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace LambdaCantor.Integer.Exceptional

def Source.residual (source : Source) (a b : ℝ) : ℝ :=
  ((source.scale : ℝ)*((source.horizontal : ℝ)+b)^source.exponent +
      ((source.vertical : ℝ)+a)^source.exponent - 3^(source.exponent*source.verticalDepth)) /
    (2*source.exponent*source.scale*(source.horizontal : ℝ)^(source.exponent-1))

def Source.remainder (source : Source) (a b : ℝ) : ℝ :=
  powerRemainder source.exponent source.vertical a /
      (2*source.exponent*source.scale*(source.horizontal : ℝ)^(source.exponent-1)) +
    powerRemainder source.exponent source.horizontal b /
      (2*source.exponent*(source.horizontal : ℝ)^(source.exponent-1)) +
    ((source.actualSlope-source.slope : ℚ) : ℝ)*a/2

def Source.normalizedFunction (source : Source) (a b : ℝ) : ℝ :=
  ((source.slope : ℝ)*a+b)/2 + source.remainder a b

theorem Source.normalizedFunction_continuous (source : Source) :
    Continuous (fun point : ℝ × ℝ => source.normalizedFunction point.1 point.2) := by
  unfold Source.normalizedFunction Source.remainder powerRemainder
  fun_prop

theorem Source.scale_positive (source : Source) : 0 < source.scale := by
  unfold Source.scale
  positivity

theorem Source.residual_normalization (source : Source)
    (exponent_positive : 0 < source.exponent) (horizontal_positive : 0 < source.horizontal)
    (a b : ℝ) :
    source.residual a b = ((source.slope : ℝ)*a+b)/2 - source.intercept + source.remainder a b := by
  have exponent_nonzero : (source.exponent : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt exponent_positive)
  have horizontal_nonzero : (source.horizontal : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt horizontal_positive)
  have scale_nonzero : (source.scale : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt source.scale_positive)
  unfold Source.residual Source.remainder Source.intercept Source.actualSlope powerRemainder
  push_cast
  field_simp [exponent_nonzero, horizontal_nonzero, scale_nonzero]
  <;> ring

theorem Source.remainder_zero (source : Source) : source.remainder 0 0 = 0 := by
  simp [Source.remainder, powerRemainder_zero]

private theorem separable_difference (firstFunction secondFunction : ℝ → ℝ)
    (firstBound secondBound linear : ℝ)
    (first_nonnegative : 0 ≤ firstBound) (second_nonnegative : 0 ≤ secondBound)
    (linear_nonnegative : 0 ≤ linear)
    (first second : ℝ × ℝ)
    (first_estimate : |firstFunction first.1-firstFunction second.1| ≤ firstBound*|first.1-second.1|)
    (second_estimate : |secondFunction first.2-secondFunction second.2| ≤ secondBound*|first.2-second.2|) :
    |(firstFunction first.1+secondFunction first.2+linear*first.1) -
      (firstFunction second.1+secondFunction second.2+linear*second.1)| ≤
      (firstBound+secondBound+linear)*dist first second := by
  have horizontal_distance : |first.1-second.1| ≤ dist first second := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have vertical_distance : |first.2-second.2| ≤ dist first second := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  have decomposition :
      (firstFunction first.1+secondFunction first.2+linear*first.1) -
        (firstFunction second.1+secondFunction second.2+linear*second.1) =
      (firstFunction first.1-firstFunction second.1) +
        (secondFunction first.2-secondFunction second.2) + linear*(first.1-second.1) := by ring
  rw [decomposition]
  have triangle := (abs_add_le
    ((firstFunction first.1-firstFunction second.1)+(secondFunction first.2-secondFunction second.2))
    (linear*(first.1-second.1))).trans
    (add_le_add (abs_add_le (firstFunction first.1-firstFunction second.1)
      (secondFunction first.2-secondFunction second.2))
      (le_refl |linear*(first.1-second.1)|))
  rw [abs_mul, abs_of_nonneg linear_nonnegative] at triangle
  nlinarith [mul_le_mul_of_nonneg_left horizontal_distance first_nonnegative,
    mul_le_mul_of_nonneg_left vertical_distance second_nonnegative,
    mul_le_mul_of_nonneg_left horizontal_distance linear_nonnegative]

/-- The exact error printed in the frozen article bounds the Lipschitz constant
of the actual normalized Fermat remainder, including the smaller rational slope. -/
theorem Source.remainder_difference (source : Source)
    (exponent_positive : 0 < source.exponent) (horizontal_positive : 0 < source.horizontal)
    (slope_ordered : source.slope ≤ source.actualSlope)
    (first second : ℝ × ℝ)
    (first_bounds : first ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (second_bounds : second ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :
    |source.remainder first.1 first.2-source.remainder second.1 second.2| ≤
      (source.error : ℝ)*dist first second := by
  have exponent_real : 0 < (source.exponent : ℝ) := by exact_mod_cast exponent_positive
  have horizontal_real : 0 < (source.horizontal : ℝ) := by exact_mod_cast horizontal_positive
  have scale_real : 0 < (source.scale : ℝ) := by exact_mod_cast source.scale_positive
  have vertical_difference : 0 ≤ ((source.vertical : ℝ)+1)^(source.exponent-1) -
      (source.vertical : ℝ)^(source.exponent-1) :=
    sub_nonneg.mpr (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _)
  have horizontal_difference : 0 ≤ ((source.horizontal : ℝ)+1)^(source.exponent-1) -
      (source.horizontal : ℝ)^(source.exponent-1) :=
    sub_nonneg.mpr (pow_le_pow_left₀ horizontal_real.le (by linarith) _)
  have slope_difference : 0 ≤ ((source.actualSlope-source.slope : ℚ) : ℝ) := by
    exact_mod_cast sub_nonneg.mpr slope_ordered
  have estimate := separable_difference
    (fun value => powerRemainder source.exponent source.vertical value /
      (2*source.exponent*source.scale*(source.horizontal : ℝ)^(source.exponent-1)))
    (fun value => powerRemainder source.exponent source.horizontal value /
      (2*source.exponent*(source.horizontal : ℝ)^(source.exponent-1)))
    (source.exponent*(((source.vertical : ℝ)+1)^(source.exponent-1) -
      (source.vertical : ℝ)^(source.exponent-1)) /
      (2*source.exponent*source.scale*(source.horizontal : ℝ)^(source.exponent-1)))
    (source.exponent*(((source.horizontal : ℝ)+1)^(source.exponent-1) -
      (source.horizontal : ℝ)^(source.exponent-1)) /
      (2*source.exponent*(source.horizontal : ℝ)^(source.exponent-1)))
    (((source.actualSlope-source.slope : ℚ) : ℝ)/2)
    (by positivity) (by positivity) (by positivity) first second
    (normalized_powerRemainder_difference source.exponent source.vertical _ (Nat.cast_nonneg _)
      (by positivity) first.1 second.1 first_bounds.1 second_bounds.1)
    (normalized_powerRemainder_difference source.exponent source.horizontal _ horizontal_real.le
      (by positivity) first.2 second.2 first_bounds.2 second_bounds.2)
  have coefficient :
      source.exponent*(((source.vertical : ℝ)+1)^(source.exponent-1) -
        (source.vertical : ℝ)^(source.exponent-1)) /
        (2*source.exponent*source.scale*(source.horizontal : ℝ)^(source.exponent-1)) +
      source.exponent*(((source.horizontal : ℝ)+1)^(source.exponent-1) -
        (source.horizontal : ℝ)^(source.exponent-1)) /
        (2*source.exponent*(source.horizontal : ℝ)^(source.exponent-1)) +
      ((source.actualSlope-source.slope : ℚ) : ℝ)/2 = (source.error : ℝ) := by
    unfold Source.error
    push_cast
    field_simp [ne_of_gt exponent_real, ne_of_gt horizontal_real, ne_of_gt scale_real]
    <;> ring
  rw [coefficient] at estimate
  simpa only [Source.remainder, div_mul_eq_mul_div] using estimate

theorem Source.error_nonnegative (source : Source)
    (exponent_positive : 0 < source.exponent) (horizontal_positive : 0 < source.horizontal)
    (slope_ordered : source.slope ≤ source.actualSlope) : 0 ≤ (source.error : ℝ) := by
  have estimate := source.remainder_difference exponent_positive horizontal_positive slope_ordered
    (1,0) (0,0) (by norm_num) (by norm_num)
  norm_num [Prod.dist_eq, Real.dist_eq] at estimate
  exact le_trans (abs_nonneg _) estimate

theorem Source.remainder_lipschitz (source : Source)
    (exponent_positive : 0 < source.exponent) (horizontal_positive : 0 < source.horizontal)
    (slope_ordered : source.slope ≤ source.actualSlope) :
    LipschitzOnWith ⟨(source.error : ℝ), source.error_nonnegative
      exponent_positive horizontal_positive slope_ordered⟩
      (fun point : ℝ × ℝ => source.remainder point.1 point.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro first first_member second second_member
  rw [Real.dist_eq]
  exact source.remainder_difference exponent_positive horizontal_positive slope_ordered
    first second first_member second_member

theorem Source.remainder_uniform_bound (source : Source)
    (exponent_positive : 0 < source.exponent) (horizontal_positive : 0 < source.horizontal)
    (slope_ordered : source.slope ≤ source.actualSlope)
    (a b : ℝ) (first_bounds : a ∈ Set.Icc (0 : ℝ) 1) (second_bounds : b ∈ Set.Icc (0 : ℝ) 1) :
    |source.remainder a b| ≤ (source.error : ℝ) := by
  have estimate := source.remainder_difference exponent_positive horizontal_positive slope_ordered
    (a,b) (0,0) ⟨first_bounds,second_bounds⟩ (by norm_num)
  rw [source.remainder_zero, sub_zero] at estimate
  have distance : dist (a,b) ((0,0) : ℝ × ℝ) ≤ 1 := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [sub_zero, abs_of_nonneg first_bounds.1, abs_of_nonneg second_bounds.1]
    exact max_le first_bounds.2 second_bounds.2
  exact estimate.trans (by
    simpa using mul_le_mul_of_nonneg_left distance
      (source.error_nonnegative exponent_positive horizontal_positive slope_ordered))

/-- Subtracting the lower-corner error and rescaling a descendant does not
increase its Lipschitz constant. This is the analytic invariance used at every return. -/
theorem Source.descendant_remainder_difference (source : Source)
    (exponent_positive : 0 < source.exponent) (horizontal_positive : 0 < source.horizontal)
    (slope_ordered : source.slope ≤ source.actualSlope)
    (u v side : ℝ) (side_positive : 0 < side)
    (u_nonnegative : 0 ≤ u) (v_nonnegative : 0 ≤ v)
    (u_upper : u+side ≤ 1) (v_upper : v+side ≤ 1)
    (first second : ℝ × ℝ)
    (first_bounds : first ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (second_bounds : second ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :
    |(source.remainder (u+side*first.1) (v+side*first.2)-source.remainder u v)/side -
      (source.remainder (u+side*second.1) (v+side*second.2)-source.remainder u v)/side| ≤
      (source.error : ℝ)*dist first second := by
  have mapped_bounds (point : ℝ × ℝ)
      (membership : point ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :
      (u+side*point.1, v+side*point.2) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    constructor <;> constructor <;>
      nlinarith [mul_nonneg side_positive.le membership.1.1,
        mul_le_mul_of_nonneg_left membership.1.2 side_positive.le,
        mul_nonneg side_positive.le membership.2.1,
        mul_le_mul_of_nonneg_left membership.2.2 side_positive.le]
  have estimate := source.remainder_difference exponent_positive horizontal_positive slope_ordered
    (u+side*first.1,v+side*first.2) (u+side*second.1,v+side*second.2)
    (mapped_bounds first first_bounds) (mapped_bounds second second_bounds)
  have coordinate_distance (offset x y : ℝ) :
      dist (offset+side*x) (offset+side*y) = side*dist x y := by
    rw [Real.dist_eq, Real.dist_eq]
    have identity : offset+side*x-(offset+side*y) = side*(x-y) := by ring
    rw [identity, abs_mul, abs_of_pos side_positive]
  have distance : dist (u+side*first.1,v+side*first.2) (u+side*second.1,v+side*second.2) ≤
      side*dist first second := by
    rw [Prod.dist_eq, coordinate_distance, coordinate_distance, Prod.dist_eq]
    exact max_le (mul_le_mul_of_nonneg_left (le_max_left _ _) side_positive.le)
      (mul_le_mul_of_nonneg_left (le_max_right _ _) side_positive.le)
  have scaled_distance := mul_le_mul_of_nonneg_left distance
    (source.error_nonnegative exponent_positive horizontal_positive slope_ordered)
  rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos side_positive]
  apply (div_le_iff₀ side_positive).mpr
  nlinarith

theorem Source.residual_zero_iff_fermat (source : Source)
    (exponent_positive : 0 < source.exponent) (horizontal_positive : 0 < source.horizontal)
    (depth_ordered : source.horizontalDepth ≤ source.verticalDepth) (a b : ℝ) :
    source.residual a b = 0 ↔
      (((source.horizontal : ℝ)+b)/3^source.horizontalDepth)^source.exponent +
        (((source.vertical : ℝ)+a)/3^source.verticalDepth)^source.exponent = 1 := by
  have exponent_real : 0 < (source.exponent : ℝ) := by exact_mod_cast exponent_positive
  have horizontal_real : 0 < (source.horizontal : ℝ) := by exact_mod_cast horizontal_positive
  have scale_real : 0 < (source.scale : ℝ) := by exact_mod_cast source.scale_positive
  have denominator_nonzero :
      2*(source.exponent : ℝ)*source.scale*(source.horizontal : ℝ)^(source.exponent-1) ≠ 0 := by positivity
  have common_power : (source.scale : ℝ)*((3 : ℝ)^source.horizontalDepth)^source.exponent =
      (3 : ℝ)^(source.exponent*source.verticalDepth) := by
    unfold Source.scale
    push_cast
    rw [← pow_mul, ← pow_add]
    congr 1
    calc
      source.exponent*(source.verticalDepth-source.horizontalDepth) +
          source.horizontalDepth*source.exponent =
        source.exponent*((source.verticalDepth-source.horizontalDepth)+source.horizontalDepth) := by ring
      _ = source.exponent*source.verticalDepth := by rw [Nat.sub_add_cancel depth_ordered]
  have first_quotient :
      (((source.horizontal : ℝ)+b)/3^source.horizontalDepth)^source.exponent =
      (source.scale : ℝ)*((source.horizontal : ℝ)+b)^source.exponent /
        (3 : ℝ)^(source.exponent*source.verticalDepth) := by
    rw [div_pow]
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    rw [← common_power]
    ring
  have second_quotient :
      (((source.vertical : ℝ)+a)/3^source.verticalDepth)^source.exponent =
      ((source.vertical : ℝ)+a)^source.exponent /
        (3 : ℝ)^(source.exponent*source.verticalDepth) := by
    rw [div_pow, ← pow_mul, Nat.mul_comm source.verticalDepth source.exponent]
  rw [first_quotient, second_quotient, ← add_div]
  unfold Source.residual
  constructor
  · intro zero
    have numerator := (div_eq_zero_iff).mp zero
    rcases numerator with numerator | impossible
    · apply (div_eq_iff (by positivity)).mpr
      nlinarith
    · exact False.elim (denominator_nonzero impossible)
  · intro equation
    have numerator := (div_eq_iff (by positivity)).mp equation
    apply div_eq_zero_iff.mpr
    left
    nlinarith

theorem Source.valid_remainder_difference (source : Source) (valid : source.Valid)
    (first second : ℝ × ℝ)
    (first_bounds : first ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (second_bounds : second ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :
    |source.remainder first.1 first.2-source.remainder second.1 second.2| ≤
      (source.error : ℝ)*dist first second := by
  rcases valid with ⟨exponent, horizontal, vertical, depths, first_prefix, second_prefix,
    first_upper, second_upper, lower_corner, upper_corner, slope_lower, slope_upper,
    slope_ordered, intercept, small_error⟩
  exact source.remainder_difference (by omega) horizontal slope_ordered
    first second first_bounds second_bounds

theorem Source.normalized_coordinateBounds (source : Source)
    (exponent_positive : 0 < source.exponent) (horizontal_positive : 0 < source.horizontal)
    (slope_ordered : source.slope ≤ source.actualSlope) :
    Classical.CoordinateBounds source.normalizedFunction
      ((source.slope : ℝ)/2-source.error) ((source.slope : ℝ)/2+source.error)
      (1/2-(source.error : ℝ)) (1/2+(source.error : ℝ)) := by
  constructor
  · intro y y_bounds first first_bounds second second_bounds ordered
    have estimate := source.remainder_difference exponent_positive horizontal_positive slope_ordered
      (second,y) (first,y) ⟨second_bounds,y_bounds⟩ ⟨first_bounds,y_bounds⟩
    have distance : dist ((second,y) : ℝ × ℝ) (first,y) = second-first := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp [abs_of_nonneg (sub_nonneg.mpr ordered),ordered]
    rw [distance] at estimate
    have bounds := abs_le.mp estimate
    unfold Source.normalizedFunction
    constructor <;> nlinarith [bounds.1, bounds.2]
  · intro x x_bounds first first_bounds second second_bounds ordered
    have estimate := source.remainder_difference exponent_positive horizontal_positive slope_ordered
      (x,second) (x,first) ⟨x_bounds,second_bounds⟩ ⟨x_bounds,first_bounds⟩
    have distance : dist ((x,second) : ℝ × ℝ) (x,first) = second-first := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp [abs_of_nonneg (sub_nonneg.mpr ordered),ordered]
    rw [distance] at estimate
    have bounds := abs_le.mp estimate
    unfold Source.normalizedFunction
    constructor <;> nlinarith [bounds.1, bounds.2]

theorem Source.normalized_uniform_approximation (source : Source)
    (exponent_positive : 0 < source.exponent) (horizontal_positive : 0 < source.horizontal)
    (slope_ordered : source.slope ≤ source.actualSlope)
    (a b : ℝ) (first_bounds : a ∈ Set.Icc (0 : ℝ) 1) (second_bounds : b ∈ Set.Icc (0 : ℝ) 1) :
    |source.normalizedFunction a b-((source.slope : ℝ)*a+b)/2| ≤ (source.error : ℝ) := by
  simpa only [Source.normalizedFunction, add_sub_cancel_left] using
    source.remainder_uniform_bound exponent_positive horizontal_positive slope_ordered
      a b first_bounds second_bounds

theorem Source.normalized_level_iff_fermat (source : Source)
    (exponent_positive : 0 < source.exponent) (horizontal_positive : 0 < source.horizontal)
    (depth_ordered : source.horizontalDepth ≤ source.verticalDepth) (a b : ℝ) :
    source.normalizedFunction a b = (source.intercept : ℝ) ↔
      (((source.horizontal : ℝ)+b)/3^source.horizontalDepth)^source.exponent +
        (((source.vertical : ℝ)+a)/3^source.verticalDepth)^source.exponent = 1 := by
  rw [← source.residual_zero_iff_fermat exponent_positive horizontal_positive depth_ordered a b]
  have normalization := source.residual_normalization exponent_positive horizontal_positive a b
  unfold Source.normalizedFunction
  constructor <;> intro equation <;> linarith

end LambdaCantor.Integer.Exceptional
