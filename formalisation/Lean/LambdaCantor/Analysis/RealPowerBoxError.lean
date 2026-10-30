import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open scoped NNReal
namespace LambdaCantor.Analysis

/-- Endpoint control also covers negative real exponents. -/
theorem rpow_le_max_endpoints {lower upper value exponent : ℝ}
    (lower_positive : 0 < lower) (membership : value ∈ Set.Icc lower upper) :
    value^exponent ≤ max (lower^exponent) (upper^exponent) := by
  by_cases nonnegative : 0 ≤ exponent
  · exact (Real.rpow_le_rpow (lower_positive.trans_le membership.1).le
      membership.2 nonnegative).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_nonpos lower_positive membership.1
      (le_of_not_ge nonnegative)).trans (le_max_left _ _)

def realPowerSecondBound (exponent base scale : ℝ) : ℝ :=
  exponent * |exponent-1| * max (base^(exponent-2)) ((base+scale)^(exponent-2))

theorem realPowerSecondBound_nonnegative {exponent base scale : ℝ}
    (exponent_greater_one : 1 < exponent) (base_positive : 0 < base) :
    0 ≤ realPowerSecondBound exponent base scale := by
  have exponent_positive : 0 < exponent := by linarith
  have left_nonnegative := Real.rpow_nonneg base_positive.le (exponent-2)
  unfold realPowerSecondBound
  exact mul_nonneg (mul_nonneg exponent_positive.le (abs_nonneg _))
    (left_nonnegative.trans (le_max_left _ _))

def realPowerSlope (exponent value : ℝ) : ℝ := exponent*value^(exponent-1)

theorem realPowerSlope_hasDerivAt (exponent value : ℝ) (positive : 0 < value) :
    HasDerivAt (realPowerSlope exponent)
      (exponent*(exponent-1)*value^(exponent-2)) value := by
  have derivative := (Real.hasDerivAt_rpow_const (p := exponent-1)
    (Or.inl (ne_of_gt positive))).const_mul exponent
  convert! derivative using 1 <;>
    simp only [realPowerSlope,show exponent-1-1 = exponent-2 by ring,mul_assoc]

/-- A bound for the actual second derivative, not an assumed Taylor oracle. -/
theorem realPowerSlope_derivative_bound {exponent base scale value : ℝ}
    (exponent_greater_one : 1 < exponent) (base_positive : 0 < base)
    (membership : value ∈ Set.Icc base (base+scale)) :
    ‖exponent*(exponent-1)*value^(exponent-2)‖ ≤
      realPowerSecondBound exponent base scale := by
  have exponent_positive : 0 < exponent := by linarith
  have value_positive := base_positive.trans_le membership.1
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos exponent_positive,
    abs_of_nonneg (Real.rpow_nonneg value_positive.le _)]
  change exponent * |exponent-1| * value^(exponent-2) ≤
    exponent * |exponent-1| * max (base^(exponent-2)) ((base+scale)^(exponent-2))
  exact mul_le_mul_of_nonneg_left
    (rpow_le_max_endpoints (exponent := exponent-2) base_positive membership)
    (mul_nonneg exponent_positive.le (abs_nonneg (exponent-1)))

theorem realPowerSlope_variation {exponent base scale first second : ℝ}
    (exponent_greater_one : 1 < exponent) (base_positive : 0 < base)
    (first_mem : first ∈ Set.Icc base (base+scale))
    (second_mem : second ∈ Set.Icc base (base+scale)) :
    |realPowerSlope exponent first-realPowerSlope exponent second| ≤
      realPowerSecondBound exponent base scale*|first-second| := by
  simpa only [Real.norm_eq_abs] using
    (convex_Icc base (base+scale)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun value membership =>
        (realPowerSlope_hasDerivAt exponent value
          (base_positive.trans_le membership.1)).hasDerivWithinAt)
      (fun value membership => realPowerSlope_derivative_bound
        exponent_greater_one base_positive membership) second_mem first_mem

def realPowerRemainder (exponent base scale parameter : ℝ) : ℝ :=
  (base+scale*parameter)^exponent-base^exponent-
    exponent*base^(exponent-1)*scale*parameter

@[simp] theorem realPowerRemainder_zero (exponent base scale : ℝ) :
    realPowerRemainder exponent base scale 0 = 0 := by
  simp [realPowerRemainder]

theorem realPowerRemainder_hasDerivAt (exponent base scale parameter : ℝ)
    (positive : 0 < base+scale*parameter) :
    HasDerivAt (realPowerRemainder exponent base scale)
      (scale*(realPowerSlope exponent (base+scale*parameter)-realPowerSlope exponent base))
      parameter := by
  have affine : HasDerivAt (fun value : ℝ => base+scale*value) scale parameter :=
    by
      convert! ((hasDerivAt_id parameter).const_mul scale).const_add base using 1 <;>
        simp only [mul_one,id_eq]
  have power := affine.rpow_const (p := exponent) (Or.inl (ne_of_gt positive))
  have linear := (hasDerivAt_id parameter).const_mul (exponent*base^(exponent-1)*scale)
  convert! (power.sub_const (base^exponent)).sub linear using 1 <;>
    try simp only [realPowerRemainder,realPowerSlope,Pi.sub_apply,id_eq,mul_one]
  all_goals ring

theorem realPowerRemainder_derivative_bound {exponent base scale parameter : ℝ}
    (exponent_greater_one : 1 < exponent) (base_positive : 0 < base)
    (scale_positive : 0 < scale) (membership : parameter ∈ Set.Icc (0 : ℝ) 1) :
    ‖scale*(realPowerSlope exponent (base+scale*parameter)-realPowerSlope exponent base)‖ ≤
      scale^2*realPowerSecondBound exponent base scale := by
  have bound_nonnegative := realPowerSecondBound_nonnegative (scale := scale)
    exponent_greater_one base_positive
  have scaled_mem : base+scale*parameter ∈ Set.Icc base (base+scale) := by
    constructor
    · linarith [mul_nonneg scale_positive.le membership.1]
    · have upper := mul_le_mul_of_nonneg_left membership.2 scale_positive.le
      nlinarith [upper]
  have variation := realPowerSlope_variation exponent_greater_one base_positive scaled_mem
    (show base ∈ Set.Icc base (base+scale) from ⟨le_rfl,by linarith⟩)
  rw [show base+scale*parameter-base = scale*parameter by ring,abs_mul,
    abs_of_pos scale_positive,abs_of_nonneg membership.1] at variation
  have uniform : |realPowerSlope exponent (base+scale*parameter)-realPowerSlope exponent base| ≤
      realPowerSecondBound exponent base scale*scale := by
    apply variation.trans
    simpa only [mul_one,mul_assoc] using
      mul_le_mul_of_nonneg_left membership.2 (mul_nonneg bound_nonnegative scale_positive.le)
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos scale_positive]
  calc
    _ ≤ scale*(realPowerSecondBound exponent base scale*scale) :=
      mul_le_mul_of_nonneg_left uniform scale_positive.le
    _ = _ := by ring

/-- The first-order remainder has a quadratic-in-scale Lipschitz constant. -/
theorem realPowerRemainder_difference {exponent base scale first second : ℝ}
    (exponent_greater_one : 1 < exponent) (base_positive : 0 < base)
    (scale_positive : 0 < scale) (first_mem : first ∈ Set.Icc (0 : ℝ) 1)
    (second_mem : second ∈ Set.Icc (0 : ℝ) 1) :
    |realPowerRemainder exponent base scale first-realPowerRemainder exponent base scale second| ≤
      (scale^2*realPowerSecondBound exponent base scale)*|first-second| := by
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun value membership => (realPowerRemainder_hasDerivAt exponent base scale value
        (by linarith [mul_nonneg scale_positive.le membership.1])).hasDerivWithinAt)
      (fun value membership => realPowerRemainder_derivative_bound
        exponent_greater_one base_positive scale_positive membership) second_mem first_mem

def realPowerBoxFunction (exponent horizontalBase verticalBase horizontalScale verticalScale normalization : ℝ)
    (point : ℝ × ℝ) : ℝ :=
  ((horizontalBase+horizontalScale*point.1)^exponent+
    (verticalBase+verticalScale*point.2)^exponent-1)/normalization

def realPowerBoxError (exponent horizontalBase verticalBase horizontalScale verticalScale normalization : ℝ)
    (point : ℝ × ℝ) : ℝ :=
  realPowerBoxFunction exponent horizontalBase verticalBase horizontalScale verticalScale normalization point-
    realPowerBoxFunction exponent horizontalBase verticalBase horizontalScale verticalScale normalization 0-
    (exponent*horizontalBase^(exponent-1)*horizontalScale*point.1+
      exponent*verticalBase^(exponent-1)*verticalScale*point.2)/normalization

def realPowerBoxErrorBound (exponent horizontalBase verticalBase horizontalScale verticalScale normalization : ℝ) : ℝ :=
  (horizontalScale^2*realPowerSecondBound exponent horizontalBase horizontalScale+
    verticalScale^2*realPowerSecondBound exponent verticalBase verticalScale)/normalization

theorem realPowerBoxError_decomposition
    (exponent horizontalBase verticalBase horizontalScale verticalScale normalization : ℝ) (point : ℝ × ℝ) :
    realPowerBoxError exponent horizontalBase verticalBase horizontalScale verticalScale normalization point =
      (realPowerRemainder exponent horizontalBase horizontalScale point.1+
        realPowerRemainder exponent verticalBase verticalScale point.2)/normalization := by
  unfold realPowerBoxError realPowerBoxFunction realPowerRemainder
  simp only [show (0 : ℝ × ℝ).1 = (0 : ℝ) from rfl,
    show (0 : ℝ × ℝ).2 = (0 : ℝ) from rfl,mul_zero,add_zero]
  ring

@[simp] theorem realPowerBoxError_zero
    (exponent horizontalBase verticalBase horizontalScale verticalScale normalization : ℝ) :
    realPowerBoxError exponent horizontalBase verticalBase horizontalScale verticalScale normalization 0 = 0 := by
  simp [realPowerBoxError]

theorem realPowerBoxErrorBound_nonnegative
    {exponent horizontalBase verticalBase horizontalScale verticalScale normalization : ℝ}
    (exponent_greater_one : 1 < exponent) (horizontal_positive : 0 < horizontalBase)
    (vertical_positive : 0 < verticalBase) (normalization_positive : 0 < normalization) :
    0 ≤ realPowerBoxErrorBound exponent horizontalBase verticalBase horizontalScale verticalScale normalization := by
  unfold realPowerBoxErrorBound
  exact div_nonneg (add_nonneg
    (mul_nonneg (sq_nonneg _) (realPowerSecondBound_nonnegative exponent_greater_one horizontal_positive))
    (mul_nonneg (sq_nonneg _) (realPowerSecondBound_nonnegative exponent_greater_one vertical_positive)))
    normalization_positive.le

theorem realPowerBoxError_difference
    {exponent horizontalBase verticalBase horizontalScale verticalScale normalization : ℝ}
    (exponent_greater_one : 1 < exponent) (horizontal_positive : 0 < horizontalBase)
    (vertical_positive : 0 < verticalBase) (horizontalScale_positive : 0 < horizontalScale)
    (verticalScale_positive : 0 < verticalScale) (normalization_positive : 0 < normalization)
    (first second : ℝ × ℝ)
    (first_mem : first ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (second_mem : second ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :
    |realPowerBoxError exponent horizontalBase verticalBase horizontalScale verticalScale normalization first-
      realPowerBoxError exponent horizontalBase verticalBase horizontalScale verticalScale normalization second| ≤
      realPowerBoxErrorBound exponent horizontalBase verticalBase horizontalScale verticalScale normalization*
        dist first second := by
  have horizontal := realPowerRemainder_difference exponent_greater_one horizontal_positive
    horizontalScale_positive first_mem.1 second_mem.1
  have vertical := realPowerRemainder_difference exponent_greater_one vertical_positive
    verticalScale_positive first_mem.2 second_mem.2
  have horizontal_nonnegative : 0 ≤ horizontalScale^2*realPowerSecondBound exponent horizontalBase horizontalScale :=
    mul_nonneg (sq_nonneg _) (realPowerSecondBound_nonnegative exponent_greater_one horizontal_positive)
  have vertical_nonnegative : 0 ≤ verticalScale^2*realPowerSecondBound exponent verticalBase verticalScale :=
    mul_nonneg (sq_nonneg _) (realPowerSecondBound_nonnegative exponent_greater_one vertical_positive)
  have horizontal_distance : |first.1-second.1| ≤ dist first second := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_left _ _
  have vertical_distance : |first.2-second.2| ≤ dist first second := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_right _ _
  have triangle := abs_add_le
    (realPowerRemainder exponent horizontalBase horizontalScale first.1-
      realPowerRemainder exponent horizontalBase horizontalScale second.1)
    (realPowerRemainder exponent verticalBase verticalScale first.2-
      realPowerRemainder exponent verticalBase verticalScale second.2)
  have numerator :
      |(realPowerRemainder exponent horizontalBase horizontalScale first.1+
        realPowerRemainder exponent verticalBase verticalScale first.2)-
        (realPowerRemainder exponent horizontalBase horizontalScale second.1+
        realPowerRemainder exponent verticalBase verticalScale second.2)| ≤
      (horizontalScale^2*realPowerSecondBound exponent horizontalBase horizontalScale+
        verticalScale^2*realPowerSecondBound exponent verticalBase verticalScale)*dist first second := by
    have rearrange : (realPowerRemainder exponent horizontalBase horizontalScale first.1+
        realPowerRemainder exponent verticalBase verticalScale first.2)-
        (realPowerRemainder exponent horizontalBase horizontalScale second.1+
        realPowerRemainder exponent verticalBase verticalScale second.2) =
      (realPowerRemainder exponent horizontalBase horizontalScale first.1-
        realPowerRemainder exponent horizontalBase horizontalScale second.1)+
      (realPowerRemainder exponent verticalBase verticalScale first.2-
        realPowerRemainder exponent verticalBase verticalScale second.2) := by ring
    rw [rearrange]
    exact triangle.trans ((add_le_add horizontal vertical).trans (by
      nlinarith [mul_le_mul_of_nonneg_left horizontal_distance horizontal_nonnegative,
        mul_le_mul_of_nonneg_left vertical_distance vertical_nonnegative]))
  rw [realPowerBoxError_decomposition,realPowerBoxError_decomposition,← sub_div,
    abs_div,abs_of_pos normalization_positive]
  have divided := div_le_div_of_nonneg_right numerator normalization_positive.le
  simpa only [realPowerBoxErrorBound,mul_div_right_comm] using divided

theorem realPowerBoxError_lipschitz
    {exponent horizontalBase verticalBase horizontalScale verticalScale normalization : ℝ}
    (exponent_greater_one : 1 < exponent) (horizontal_positive : 0 < horizontalBase)
    (vertical_positive : 0 < verticalBase) (horizontalScale_positive : 0 < horizontalScale)
    (verticalScale_positive : 0 < verticalScale) (normalization_positive : 0 < normalization) :
    LipschitzOnWith
      ⟨realPowerBoxErrorBound exponent horizontalBase verticalBase horizontalScale verticalScale normalization,
        realPowerBoxErrorBound_nonnegative exponent_greater_one horizontal_positive vertical_positive normalization_positive⟩
      (realPowerBoxError exponent horizontalBase verticalBase horizontalScale verticalScale normalization)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro first first_mem second second_mem
  rw [Real.dist_eq]
  exact realPowerBoxError_difference exponent_greater_one horizontal_positive vertical_positive
    horizontalScale_positive verticalScale_positive normalization_positive first second first_mem second_mem

/-- Replacing a frozen derivative by a reference slope costs exactly the two
coefficient errors. The constant level shift has no Lipschitz cost. -/
theorem referenceSlope_error_difference
    (function : (ℝ × ℝ) → ℝ) (constant horizontal vertical slope bound : ℝ)
    (first second : ℝ × ℝ)
    (frozen_error :
      |(function first-constant-(horizontal*first.1+vertical*first.2))-
        (function second-constant-(horizontal*second.1+vertical*second.2))| ≤
        bound*dist first second) :
    |(function first-constant-(slope*first.1+first.2)/2)-
      (function second-constant-(slope*second.1+second.2)/2)| ≤
      (bound+|horizontal-slope/2|+|vertical-1/2|)*dist first second := by
  have identity :
      (function first-constant-(slope*first.1+first.2)/2)-
        (function second-constant-(slope*second.1+second.2)/2) =
      ((function first-constant-(horizontal*first.1+vertical*first.2))-
        (function second-constant-(horizontal*second.1+vertical*second.2)))+
      (horizontal-slope/2)*(first.1-second.1)+(vertical-1/2)*(first.2-second.2) := by ring
  have horizontal_distance : |first.1-second.1| ≤ dist first second := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_left _ _
  have vertical_distance : |first.2-second.2| ≤ dist first second := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_right _ _
  rw [identity]
  have first_triangle := abs_add_le
    ((function first-constant-(horizontal*first.1+vertical*first.2))-
      (function second-constant-(horizontal*second.1+vertical*second.2)))
    ((horizontal-slope/2)*(first.1-second.1))
  have second_triangle := abs_add_le
    (((function first-constant-(horizontal*first.1+vertical*first.2))-
      (function second-constant-(horizontal*second.1+vertical*second.2)))+
      (horizontal-slope/2)*(first.1-second.1))
    ((vertical-1/2)*(first.2-second.2))
  simp only [abs_mul] at first_triangle second_triangle
  nlinarith [first_triangle,second_triangle,
    mul_le_mul_of_nonneg_left horizontal_distance (abs_nonneg (horizontal-slope/2)),
    mul_le_mul_of_nonneg_left vertical_distance (abs_nonneg (vertical-1/2))]

def realPowerBoxReferenceError
    (exponent horizontalBase verticalBase horizontalScale verticalScale normalization slope : ℝ)
    (point : ℝ × ℝ) : ℝ :=
  realPowerBoxFunction exponent horizontalBase verticalBase horizontalScale verticalScale normalization point-
    realPowerBoxFunction exponent horizontalBase verticalBase horizontalScale verticalScale normalization 0-
    (slope*point.1+point.2)/2

@[simp] theorem realPowerBoxReferenceError_zero
    (exponent horizontalBase verticalBase horizontalScale verticalScale normalization slope : ℝ) :
    realPowerBoxReferenceError exponent horizontalBase verticalBase horizontalScale verticalScale normalization slope 0 = 0 := by
  simp [realPowerBoxReferenceError]

theorem realPowerBoxReferenceError_normalization
    (exponent horizontalBase verticalBase horizontalScale verticalScale normalization slope : ℝ)
    (point : ℝ × ℝ) :
    realPowerBoxFunction exponent horizontalBase verticalBase horizontalScale verticalScale normalization point =
      realPowerBoxFunction exponent horizontalBase verticalBase horizontalScale verticalScale normalization 0+
        (slope*point.1+point.2)/2+
        realPowerBoxReferenceError exponent horizontalBase verticalBase horizontalScale verticalScale normalization slope point := by
  unfold realPowerBoxReferenceError
  ring

def realPowerBoxReferenceErrorBound
    (exponent horizontalBase verticalBase horizontalScale verticalScale normalization slope : ℝ) : ℝ :=
  realPowerBoxErrorBound exponent horizontalBase verticalBase horizontalScale verticalScale normalization+
    |exponent*horizontalBase^(exponent-1)*horizontalScale/normalization-slope/2|+
    |exponent*verticalBase^(exponent-1)*verticalScale/normalization-1/2|

theorem realPowerBoxReferenceErrorBound_nonnegative
    {exponent horizontalBase verticalBase horizontalScale verticalScale normalization slope : ℝ}
    (exponent_greater_one : 1 < exponent) (horizontal_positive : 0 < horizontalBase)
    (vertical_positive : 0 < verticalBase) (normalization_positive : 0 < normalization) :
    0 ≤ realPowerBoxReferenceErrorBound exponent horizontalBase verticalBase horizontalScale verticalScale normalization slope := by
  exact add_nonneg (add_nonneg
    (realPowerBoxErrorBound_nonnegative exponent_greater_one horizontal_positive vertical_positive normalization_positive)
    (abs_nonneg _)) (abs_nonneg _)

/-- The coefficient discretization error needed by rational-slope return
atlases is added to the actual Hessian remainder bound. -/
theorem realPowerBoxReferenceError_difference
    {exponent horizontalBase verticalBase horizontalScale verticalScale normalization : ℝ}
    (exponent_greater_one : 1 < exponent) (horizontal_positive : 0 < horizontalBase)
    (vertical_positive : 0 < verticalBase) (horizontalScale_positive : 0 < horizontalScale)
    (verticalScale_positive : 0 < verticalScale) (normalization_positive : 0 < normalization)
    (slope : ℝ) (first second : ℝ × ℝ)
    (first_mem : first ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (second_mem : second ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :
    |realPowerBoxReferenceError exponent horizontalBase verticalBase horizontalScale verticalScale normalization slope first-
      realPowerBoxReferenceError exponent horizontalBase verticalBase horizontalScale verticalScale normalization slope second| ≤
      realPowerBoxReferenceErrorBound exponent horizontalBase verticalBase horizontalScale verticalScale normalization slope*
        dist first second := by
  apply referenceSlope_error_difference
    (realPowerBoxFunction exponent horizontalBase verticalBase horizontalScale verticalScale normalization)
    (realPowerBoxFunction exponent horizontalBase verticalBase horizontalScale verticalScale normalization 0)
    (exponent*horizontalBase^(exponent-1)*horizontalScale/normalization)
    (exponent*verticalBase^(exponent-1)*verticalScale/normalization)
    slope (realPowerBoxErrorBound exponent horizontalBase verticalBase horizontalScale verticalScale normalization)
    first second
  have horizontal_identity (point : ℝ × ℝ) :
      realPowerBoxFunction exponent horizontalBase verticalBase horizontalScale verticalScale normalization point-
        realPowerBoxFunction exponent horizontalBase verticalBase horizontalScale verticalScale normalization 0-
        ((exponent*horizontalBase^(exponent-1)*horizontalScale/normalization)*point.1+
          (exponent*verticalBase^(exponent-1)*verticalScale/normalization)*point.2) =
      realPowerBoxError exponent horizontalBase verticalBase horizontalScale verticalScale normalization point := by
    unfold realPowerBoxError
    ring
  rw [horizontal_identity,horizontal_identity]
  exact realPowerBoxError_difference exponent_greater_one horizontal_positive vertical_positive
    horizontalScale_positive verticalScale_positive normalization_positive first second first_mem second_mem

theorem realPowerBoxReferenceError_lipschitz
    {exponent horizontalBase verticalBase horizontalScale verticalScale normalization slope : ℝ}
    (exponent_greater_one : 1 < exponent) (horizontal_positive : 0 < horizontalBase)
    (vertical_positive : 0 < verticalBase) (horizontalScale_positive : 0 < horizontalScale)
    (verticalScale_positive : 0 < verticalScale) (normalization_positive : 0 < normalization) :
    LipschitzOnWith
      ⟨realPowerBoxReferenceErrorBound exponent horizontalBase verticalBase horizontalScale verticalScale normalization slope,
        realPowerBoxReferenceErrorBound_nonnegative exponent_greater_one horizontal_positive vertical_positive normalization_positive⟩
      (realPowerBoxReferenceError exponent horizontalBase verticalBase horizontalScale verticalScale normalization slope)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro first first_mem second second_mem
  rw [Real.dist_eq]
  exact realPowerBoxReferenceError_difference exponent_greater_one horizontal_positive vertical_positive
    horizontalScale_positive verticalScale_positive normalization_positive slope first second first_mem second_mem

end LambdaCantor.Analysis
