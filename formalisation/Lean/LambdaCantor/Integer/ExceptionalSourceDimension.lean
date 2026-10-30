import LambdaCantor.Integer.ExceptionalAtlasBridge
import LambdaCantor.Integer.ExceptionalNonlinearError
import LambdaCantor.Last.AtlasOnDust
import LambdaCantor.Integer.TernaryPrefixSoundness
import Mathlib.Topology.MetricSpace.Antilipschitz

noncomputable section
namespace LambdaCantor.Integer.Exceptional

def Source.embedding (source : Source) (point : ℝ × ℝ) : ℝ × ℝ :=
  (((source.horizontal : ℝ)+point.2)/3^source.horizontalDepth,
   ((source.vertical : ℝ)+point.1)/3^source.verticalDepth)

theorem Source.embedding_antilipschitz (source : Source)
    (depths : source.horizontalDepth ≤ source.verticalDepth) :
    AntilipschitzWith (⟨(3:ℝ)^source.verticalDepth,by positivity⟩ : NNReal) source.embedding := by
  apply AntilipschitzWith.of_le_mul_dist
  intro first second
  change dist first second ≤ (3:ℝ)^source.verticalDepth *
    dist (source.embedding first) (source.embedding second)
  have first_coordinate : |(source.embedding first).1-(source.embedding second).1| ≤
      dist (source.embedding first) (source.embedding second) := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_left _ _
  have second_coordinate : |(source.embedding first).2-(source.embedding second).2| ≤
      dist (source.embedding first) (source.embedding second) := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_right _ _
  have first_identity : (source.embedding first).1-(source.embedding second).1 =
      (first.2-second.2)/(3:ℝ)^source.horizontalDepth := by unfold Source.embedding; ring
  have second_identity : (source.embedding first).2-(source.embedding second).2 =
      (first.1-second.1)/(3:ℝ)^source.verticalDepth := by unfold Source.embedding; ring
  rw [first_identity,abs_div,abs_of_pos (by positivity : 0 < (3:ℝ)^source.horizontalDepth)] at first_coordinate
  rw [second_identity,abs_div,abs_of_pos (by positivity : 0 < (3:ℝ)^source.verticalDepth)] at second_coordinate
  have first_bound := (div_le_iff₀ (by positivity : 0 < (3:ℝ)^source.horizontalDepth)).mp first_coordinate
  have second_bound := (div_le_iff₀ (by positivity : 0 < (3:ℝ)^source.verticalDepth)).mp second_coordinate
  have powers : (3:ℝ)^source.horizontalDepth ≤ (3:ℝ)^source.verticalDepth :=
    pow_le_pow_right₀ (by norm_num) depths
  have scaled := mul_le_mul_of_nonneg_left powers
    (dist_nonneg (x := source.embedding first) (y := source.embedding second))
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
  change max |first.1-second.1| |first.2-second.2| ≤
    (3:ℝ)^source.verticalDepth * dist (source.embedding first) (source.embedding second)
  exact max_le (by nlinarith [second_bound]) (by nlinarith [first_bound,scaled])

theorem Source.positive_dimension_normalized_fibre (source : Source) (valid : source.Valid)
    (levels : Set ℝ) (atlas : Last.FiniteReturnAtlas (1/3) (slopeLinear source.slope) levels)
    (depth_matches : atlas.maxDepth = source.returnDepth)
    (margin_matches : atlas.margin = 1/100000)
    (initial_level : (source.intercept : ℝ) ∈ levels)
    (levels_bounded : ∀ level ∈ levels, 0 ≤ level ∧ level ≤ ((source.slope : ℝ)+1)/2) :
    0 < dimH {point : ℝ × ℝ | point ∈ Last.cantorDust (1/3) ∧
      (((source.horizontal : ℝ)+point.2)/3^source.horizontalDepth)^source.exponent +
        (((source.vertical : ℝ)+point.1)/3^source.verticalDepth)^source.exponent = 1} := by
  rcases valid with ⟨exponent,horizontal,vertical,depths,first_prefix,second_prefix,
    first_upper,second_upper,lower_corner,upper_corner,slope_lower,slope_upper,
    slope_ordered,intercept,small_error⟩
  have exponent_positive : 0 < source.exponent := by omega
  have slope_positive : (0:ℝ) < source.slope := by exact_mod_cast (lt_trans (by norm_num) slope_lower)
  have error_nonnegative := source.error_nonnegative exponent_positive horizontal slope_ordered
  let bound : NNReal := ⟨(source.error : ℝ),error_nonnegative⟩
  have small_real : (3:ℝ)^source.returnDepth*(source.error : ℝ) < 1/100000 := by
    have converted : (((3 : ℚ)^source.returnDepth*source.error : ℚ) : ℝ) <
        ((1/100000 : ℚ) : ℝ) := Rat.cast_lt.mpr small_error
    push_cast at converted
    exact converted
  have small : (bound : ℝ) < atlas.margin*(1/3:ℝ)^atlas.maxDepth := by
    rw [depth_matches,margin_matches]
    change (source.error : ℝ) < (1/100000:ℝ)*(1/3:ℝ)^source.returnDepth
    rw [div_pow]
    simp only [one_pow, mul_one_div]
    apply (lt_div_iff₀ (by positivity : 0 < (3:ℝ)^source.returnDepth)).mpr
    nlinarith
  have lipschitz : LipschitzOnWith bound (fun point : ℝ × ℝ => source.remainder point.1 point.2)
      (Last.cantorDust (1/3)) := by
    apply (source.remainder_lipschitz exponent_positive horizontal slope_ordered).mono
    intro point membership
    exact ⟨LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) membership.1,
      LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) membership.2⟩
  have linear_bound : ∀ point ∈ Last.cantorDust (1/3),
      |slopeLinear (source.slope : ℝ) point| ≤ ((source.slope : ℝ)+1)/2 := by
    intro point membership
    have first := LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) membership.1
    have second := LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) membership.2
    rw [slopeLinear_apply, abs_of_nonneg (div_nonneg
      (add_nonneg (mul_nonneg slope_positive.le first.1) second.1) (by norm_num))]
    have product_upper : (source.slope : ℝ) * point.1 ≤ (source.slope : ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left first.2 slope_positive.le
    exact div_le_div_of_nonneg_right (add_le_add product_upper second.2) (by norm_num)
  have dimension := atlas.positive_dimension_on_dust (by norm_num) (by norm_num) bound small
    (((source.slope : ℝ)+1)/2) (((source.slope : ℝ)+1)/2)
    (by positivity) (by positivity) linear_bound
    (fun level membership => by
      rw [abs_of_nonneg (levels_bounded level membership).1]
      exact (levels_bounded level membership).2)
    (fun point : ℝ × ℝ => source.remainder point.1 point.2) lipschitz source.remainder_zero
    source.intercept initial_level
  apply dimension.trans_le (dimH_mono ?_)
  intro point membership
  refine ⟨membership.1, ?_⟩
  apply (source.normalized_level_iff_fermat exponent_positive horizontal depths point.1 point.2).mp
  simpa only [Source.normalizedFunction,slopeLinear_apply] using membership.2

theorem Source.positive_dimension (source : Source) (valid : source.Valid)
    (levels : Set ℝ) (atlas : Last.FiniteReturnAtlas (1/3) (slopeLinear source.slope) levels)
    (depth_matches : atlas.maxDepth = source.returnDepth)
    (margin_matches : atlas.margin = 1/100000)
    (initial_level : (source.intercept : ℝ) ∈ levels)
    (levels_bounded : ∀ level ∈ levels, 0 ≤ level ∧ level ≤ ((source.slope : ℝ)+1)/2) :
    0 < dimH (intersection (source.exponent : ℝ) (1/3)) := by
  have dimension := source.positive_dimension_normalized_fibre valid levels atlas
    depth_matches margin_matches initial_level levels_bounded
  rcases valid with ⟨exponent,horizontal,vertical,depths,first_prefix,second_prefix,remaining⟩
  apply dimension.trans_le ((source.embedding_antilipschitz depths).le_dimH_image _ |>.trans (dimH_mono ?_))
  rintro point ⟨original,membership,rfl⟩
  refine ⟨ternaryPrefix_cantor_embedding _ _ first_prefix _ membership.1.2,
    ternaryPrefix_cantor_embedding _ _ second_prefix _ membership.1.1, ?_⟩
  simpa only [Source.embedding,Real.rpow_natCast] using membership.2

end LambdaCantor.Integer.Exceptional
