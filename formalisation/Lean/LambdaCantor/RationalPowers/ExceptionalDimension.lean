import LambdaCantor.RationalPowers.ExceptionalEnclosureSoundness
import LambdaCantor.Integer.ExceptionalIntervals
import LambdaCantor.Integer.ExceptionalAtlasBridge
import LambdaCantor.Integer.TernaryPrefixSoundness
import LambdaCantor.Last.AtlasOnDust
import Mathlib.Topology.MetricSpace.Antilipschitz

noncomputable section
open scoped NNReal
namespace LambdaCantor.RationalPowers.Exceptional
open LambdaCantor.Integer.Exceptional

def PowerSource.actualFunction (source : PowerSource) : (ℝ × ℝ) → ℝ :=
  Analysis.realPowerBoxFunction source.exponent source.horizontalBase source.verticalBase
    source.horizontalScale source.verticalScale source.normalization

def PowerSource.embedding (source : PowerSource) (point : ℝ × ℝ) : ℝ × ℝ :=
  (((source.horizontal : ℝ)+point.1)/3^source.horizontalDepth,
    ((source.vertical : ℝ)+point.2)/3^source.verticalDepth)

theorem PowerSource.embedding_coordinates (source : PowerSource) (point : ℝ × ℝ) :
    (source.horizontalBase : ℝ)+(source.horizontalScale : ℝ)*point.1 = (source.embedding point).1 ∧
    (source.verticalBase : ℝ)+(source.verticalScale : ℝ)*point.2 = (source.embedding point).2 := by
  unfold PowerSource.horizontalBase PowerSource.verticalBase PowerSource.horizontalScale
    PowerSource.verticalScale PowerSource.embedding
  push_cast
  constructor <;> ring

theorem PowerSource.embedding_antilipschitz (source : PowerSource) :
    AntilipschitzWith
      (⟨(3 : ℝ)^(max source.horizontalDepth source.verticalDepth),by positivity⟩ : NNReal)
      source.embedding := by
  apply AntilipschitzWith.of_le_mul_dist
  intro first second
  change dist first second ≤ (3 : ℝ)^(max source.horizontalDepth source.verticalDepth) *
    dist (source.embedding first) (source.embedding second)
  have horizontal_distance : |(source.embedding first).1-(source.embedding second).1| ≤
      dist (source.embedding first) (source.embedding second) := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_left _ _
  have vertical_distance : |(source.embedding first).2-(source.embedding second).2| ≤
      dist (source.embedding first) (source.embedding second) := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_right _ _
  have horizontal_identity : (source.embedding first).1-(source.embedding second).1 =
      (first.1-second.1)/(3 : ℝ)^source.horizontalDepth := by unfold PowerSource.embedding; ring
  have vertical_identity : (source.embedding first).2-(source.embedding second).2 =
      (first.2-second.2)/(3 : ℝ)^source.verticalDepth := by unfold PowerSource.embedding; ring
  rw [horizontal_identity,abs_div,abs_of_pos (by positivity : 0 < (3 : ℝ)^source.horizontalDepth)]
    at horizontal_distance
  rw [vertical_identity,abs_div,abs_of_pos (by positivity : 0 < (3 : ℝ)^source.verticalDepth)]
    at vertical_distance
  have horizontal_bound := (div_le_iff₀ (by positivity : 0 < (3 : ℝ)^source.horizontalDepth)).mp
    horizontal_distance
  have vertical_bound := (div_le_iff₀ (by positivity : 0 < (3 : ℝ)^source.verticalDepth)).mp
    vertical_distance
  have horizontal_power := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
    (Nat.le_max_left source.horizontalDepth source.verticalDepth)
  have vertical_power := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
    (Nat.le_max_right source.horizontalDepth source.verticalDepth)
  have horizontal_scaled := mul_le_mul_of_nonneg_left horizontal_power
    (dist_nonneg (x := source.embedding first) (y := source.embedding second))
  have vertical_scaled := mul_le_mul_of_nonneg_left vertical_power
    (dist_nonneg (x := source.embedding first) (y := source.embedding second))
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
  exact max_le (by nlinarith) (by nlinarith)

theorem PowerSource.initial_level_mem (source : PowerSource) (valid : source.Valid) :
    -source.actualFunction 0 ∈ switchLevels source.slope := by
  have bounds := source.realBounds valid
  have normalization_positive := (source.real_geometry valid).2.2.2.2.2
  have level_identity : -source.actualFunction 0 =
      (1-(source.horizontalBase : ℝ)^(source.exponent : ℝ)-
        (source.verticalBase : ℝ)^(source.exponent : ℝ))/(source.normalization : ℝ) := by
    unfold PowerSource.actualFunction Analysis.realPowerBoxFunction
    simp only [show (0 : ℝ × ℝ).1 = (0 : ℝ) from rfl,
      show (0 : ℝ × ℝ).2 = (0 : ℝ) from rfl,mul_zero,add_zero]
    ring
  have level_bounds : (source.levelLower : ℝ) ≤ -source.actualFunction 0 ∧
      -source.actualFunction 0 ≤ (source.levelUpper : ℝ) := by
    rw [level_identity]
    unfold PowerSource.levelLower PowerSource.levelUpper
    push_cast
    constructor <;> apply div_le_div_of_nonneg_right _ normalization_positive.le
    · linarith [bounds.horizontalValue.2,bounds.verticalValue.2]
    · linarith [bounds.horizontalValue.1,bounds.verticalValue.1]
  rcases valid.2.2.2 with first | second | third
  · have interval : (1/3 : ℝ) < source.levelLower ∧
        (source.levelUpper : ℝ) < ((source.slope : ℝ)+1)/6 := by
      constructor
      · simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
          (Rat.cast_lt (K := ℝ)).mpr first.1
      · exact_mod_cast first.2
    exact Or.inl (Or.inl ⟨interval.1.le.trans level_bounds.1,level_bounds.2.trans interval.2.le⟩)
  · have interval : (source.slope : ℝ)/3 < source.levelLower ∧
        (source.levelUpper : ℝ) < ((source.slope : ℝ)+3)/6 := by exact_mod_cast second
    exact Or.inl (Or.inr ⟨interval.1.le.trans level_bounds.1,level_bounds.2.trans interval.2.le⟩)
  · have interval : ((source.slope : ℝ)+1)/3 < source.levelLower ∧
        (source.levelUpper : ℝ) < (3*(source.slope : ℝ)+1)/6 := by exact_mod_cast third
    exact Or.inr ⟨interval.1.le.trans level_bounds.1,level_bounds.2.trans interval.2.le⟩

theorem PowerSource.actual_error_lipschitz (source : PowerSource) (valid : source.Valid) :
    LipschitzOnWith
      (⟨(source.error : ℝ),by exact_mod_cast valid.2.2.1.2.2.2.2.2.2.1⟩ : NNReal)
      (fun point => source.actualFunction point-source.actualFunction 0-slopeLinear source.slope point)
      (Last.cantorDust (1/3)) := by
  have geometry := source.real_geometry valid
  have reference_bound := source.reference_error_bound valid
  apply LipschitzOnWith.of_dist_le_mul
  intro first first_mem second second_mem
  rw [Real.dist_eq]
  change |(source.actualFunction first - source.actualFunction 0 - slopeLinear source.slope first) -
    (source.actualFunction second - source.actualFunction 0 - slopeLinear source.slope second)| ≤
      (source.error : ℝ) * dist first second
  have first_bounds : first ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
    ⟨cantorSet_subset_unitInterval (by norm_num) (by norm_num) first_mem.1,
      cantorSet_subset_unitInterval (by norm_num) (by norm_num) first_mem.2⟩
  have second_bounds : second ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
    ⟨cantorSet_subset_unitInterval (by norm_num) (by norm_num) second_mem.1,
      cantorSet_subset_unitInterval (by norm_num) (by norm_num) second_mem.2⟩
  have difference := Analysis.realPowerBoxReferenceError_difference geometry.1 geometry.2.1
    geometry.2.2.1 geometry.2.2.2.1 geometry.2.2.2.2.1 geometry.2.2.2.2.2
    (source.slope : ℝ) first second first_bounds second_bounds
  have normalized := difference.trans (mul_le_mul_of_nonneg_right reference_bound (dist_nonneg))
  simpa only [PowerSource.actualFunction, Analysis.realPowerBoxReferenceError,
    slopeLinear_apply] using normalized

/-- A genuine finite atlas yields positive dimension on the real-power curve
inside the two legal Cantor cylinders. No algebraic-source perfectness or
assumed positive-dimensional fibre is used. -/
theorem PowerSource.positive_dimension (source : PowerSource) (valid : source.Valid)
    (atlas : Last.FiniteReturnAtlas (1/3) (slopeLinear source.slope) (switchLevels source.slope))
    (depth_matches : atlas.maxDepth = source.returnDepth)
    (margin_matches : atlas.margin = (source.margin : ℝ)) :
    0 < dimH (intersection (source.exponent : ℝ) (1/3)) := by
  obtain ⟨_,_,_,_,horizontal_prefix,vertical_prefix,_,_,slope_lower,slope_upper,_,_⟩ := valid.1
  obtain ⟨_,_,_,_,_,_,error_nonnegative,small_error⟩ := valid.2.2.1
  have slope_real : (1 : ℝ) < source.slope := by exact_mod_cast slope_lower
  have slope_upper_real : (source.slope : ℝ) < 3 := by exact_mod_cast slope_upper
  have slope_nonnegative : (0 : ℝ) ≤ source.slope := by linarith
  have error_real : (0 : ℝ) ≤ source.error := by exact_mod_cast error_nonnegative
  let bound : NNReal := ⟨(source.error : ℝ),error_real⟩
  have small_real : (3 : ℝ)^source.returnDepth*(source.error : ℝ) < (source.margin : ℝ) := by
    exact_mod_cast small_error
  have small : (bound : ℝ) < atlas.margin*(1/3 : ℝ)^atlas.maxDepth := by
    rw [depth_matches,margin_matches]
    change (source.error : ℝ) < (source.margin : ℝ)*(1/3 : ℝ)^source.returnDepth
    rw [div_pow]
    simp only [one_pow,mul_one_div]
    apply (lt_div_iff₀ (by positivity : 0 < (3 : ℝ)^source.returnDepth)).mpr
    nlinarith
  have linear_bound : ∀ point ∈ Last.cantorDust (1/3),
      |slopeLinear source.slope point| ≤ ((source.slope : ℝ)+1)/2 := by
    intro point member
    have first := cantorSet_subset_unitInterval (by norm_num) (by norm_num) member.1
    have second := cantorSet_subset_unitInterval (by norm_num) (by norm_num) member.2
    rw [slopeLinear_apply, abs_of_nonneg (div_nonneg
      (add_nonneg (mul_nonneg slope_nonnegative first.1) second.1) (by norm_num))]
    have product_upper : (source.slope : ℝ) * point.1 ≤ (source.slope : ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left first.2 slope_nonnegative
    exact div_le_div_of_nonneg_right (add_le_add product_upper second.2) (by norm_num)
  have dimension := atlas.positive_dimension_actual_fibre (by norm_num) (by norm_num) bound small
    (((source.slope : ℝ)+1)/2) (((source.slope : ℝ)+1)/2)
    (by positivity) (by positivity) linear_bound
    (fun level member => by
      have bounds := switch_levels_bounded _ slope_real slope_upper_real level member
      rw [abs_of_nonneg bounds.1]
      exact bounds.2)
    source.actualFunction (source.actual_error_lipschitz valid) 0
    (by simpa only [zero_sub] using source.initial_level_mem valid)
  apply dimension.trans_le ((source.embedding_antilipschitz).le_dimH_image _ |>.trans (dimH_mono ?_))
  rintro point ⟨original,member,rfl⟩
  refine ⟨Integer.ternaryPrefix_cantor_embedding _ _ horizontal_prefix _ member.1.1,
    Integer.ternaryPrefix_cantor_embedding _ _ vertical_prefix _ member.1.2,?_⟩
  have equation := member.2
  change (((source.horizontalBase : ℝ)+(source.horizontalScale : ℝ)*original.1)^(source.exponent : ℝ) +
    ((source.verticalBase : ℝ)+(source.verticalScale : ℝ)*original.2)^(source.exponent : ℝ)-1) /
    (source.normalization : ℝ) = 0 at equation
  have numerator_zero := (div_eq_zero_iff.mp equation).resolve_right
    (ne_of_gt (source.real_geometry valid).2.2.2.2.2)
  have coordinates := source.embedding_coordinates original
  rw [coordinates.1,coordinates.2] at numerator_zero
  linarith

end LambdaCantor.RationalPowers.Exceptional
