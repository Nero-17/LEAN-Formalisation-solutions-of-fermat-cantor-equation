import LambdaCantor.Certificates.IntegerSmallSources
import LambdaCantor.Classical.GeneralCoverLocal
import LambdaCantor.Classical.Cylinders
import LambdaCantor.Classical.DerivativeLocalization
import LambdaCantor.Classical.GoodSlopeIsolation
import LambdaCantor.Integer.FermatTangent
import LambdaCantor.Last.ReturnWords
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
namespace LambdaCantor.Integer

def cubicFunction (first second : ℝ) : ℝ := (72 + first)^3 + (54 + second)^3 - 81^3
def cubicSource : Set (ℝ × ℝ) := Classical.cantorLevel cubicFunction 0
def cubicEmbedding (point : ℝ × ℝ) : ℝ × ℝ := ((54+point.2)/81, (72+point.1)/81)
def cubicTangent (point : ℝ × ℝ) : ℝ := (72+point.1)^2/(54+point.2)^2

theorem cubicFunction_continuous : Continuous (fun point : ℝ × ℝ => cubicFunction point.1 point.2) := by
  unfold cubicFunction
  fun_prop

theorem cubic_horizontal_derivative (first second : ℝ) :
    HasDerivAt (fun value => cubicFunction value second) (3*(72+first)^2) first := by
  simpa [cubicFunction] using
    ((((hasDerivAt_id first).const_add 72).pow 3).add_const ((54+second)^3)).sub_const (81^3)

theorem cubic_vertical_derivative (first second : ℝ) :
    HasDerivAt (fun value => cubicFunction first value) (3*(54+second)^2) second := by
  simpa [cubicFunction] using
    ((((hasDerivAt_id second).const_add 54).pow 3).const_add ((72+first)^3)).sub_const (81^3)

theorem cubic_coordinate_bounds : Classical.CoordinateBounds cubicFunction 15552 15987 8748 9075 := by
  apply Classical.coordinateBounds_of_hasDerivAt cubicFunction
    (fun first _ => 3*(72+first)^2) (fun _ second => 3*(54+second)^2)
  · intro first _ second _; exact cubic_horizontal_derivative first second
  · intro first _ second _; exact cubic_vertical_derivative first second
  · intro first first_mem second second_mem
    constructor <;> nlinarith [first_mem.1,first_mem.2, sq_nonneg first,
      mul_nonneg (sub_nonneg.mpr first_mem.2) (show 0 ≤ first+145 by linarith [first_mem.1])]
  · intro first first_mem second second_mem
    constructor <;> nlinarith [second_mem.1,second_mem.2, sq_nonneg second,
      mul_nonneg (sub_nonneg.mpr second_mem.2) (show 0 ≤ second+109 by linarith [second_mem.1])]

theorem cubic_source_nonempty : cubicSource.Nonempty := by
  obtain ⟨first,second,first_mem,second_mem,equation⟩ := Classical.general_cantor_level_local
    cubicFunction cubicFunction_continuous.continuousOn 15552 15987 8748 9075 cubic_coordinate_bounds
    (by norm_num) (by norm_num) 0 0 1 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [cubicFunction]) (by norm_num [cubicFunction])
  refine ⟨(first,second), ⟨⟨?_,?_⟩,?_⟩⟩
  · rwa [cantorSet_third_eq]
  · rwa [cantorSet_third_eq]
  · simpa using equation

theorem cubic_source_compact : IsCompact cubicSource := by
  exact (Last.isCompact_cantorDust (by norm_num : (0 : ℝ) ≤ 1/3) (by norm_num)).inter_right
    (isClosed_eq cubicFunction_continuous continuous_const)

theorem cubic_source_bounds {point : ℝ × ℝ} (membership : point ∈ cubicSource) :
    point.1 ∈ Set.Icc (0 : ℝ) 1 ∧ point.2 ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨cantorSet_subset_unitInterval (by norm_num) (by norm_num) membership.1.1,
    cantorSet_subset_unitInterval (by norm_num) (by norm_num) membership.1.2⟩

theorem cubic_tangent_good {point : ℝ × ℝ} (membership : point ∈ cubicSource) :
    GoodSlope (cubicTangent point) := by
  have bounds := cubic_source_bounds membership
  have denominator_positive : 0 < (54+point.2)^2 := by
    have := bounds.2.1
    positivity
  have first_lower : (72:ℝ)^2 ≤ (72+point.1)^2 := by nlinarith [bounds.1.1, sq_nonneg point.1]
  have first_upper : (72+point.1)^2 ≤ (73:ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr bounds.1.2) (show 0 ≤ point.1+145 by linarith [bounds.1.1])]
  have second_lower : (54:ℝ)^2 ≤ (54+point.2)^2 := by nlinarith [bounds.2.1, sq_nonneg point.2]
  have second_upper : (54+point.2)^2 ≤ (55:ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr bounds.2.2) (show 0 ≤ point.2+109 by linarith [bounds.2.1])]
  apply Or.inr; apply Or.inr; apply Or.inl
  constructor
  · apply (lt_div_iff₀ denominator_positive).mpr; nlinarith
  · apply (div_lt_iff₀ denominator_positive).mpr; nlinarith

theorem cubic_hasFDerivAt (point : ℝ × ℝ) :
    ∃ derivative : (ℝ × ℝ) →L[ℝ] ℝ,
      HasFDerivAt (fun point : ℝ × ℝ => cubicFunction point.1 point.2) derivative point ∧
      ∀ direction, derivative direction = 3*(72+point.1)^2*direction.1 + 3*(54+point.2)^2*direction.2 := by
  have first := (cubic_horizontal_derivative point.1 0).hasFDerivAt.comp point
    (hasFDerivAt_fst : HasFDerivAt (fun point : ℝ × ℝ => point.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) point)
  have second := (cubic_vertical_derivative 0 point.2).hasFDerivAt.comp point
    (hasFDerivAt_snd : HasFDerivAt (fun point : ℝ × ℝ => point.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) point)
  have combined := (first.add second).sub_const (cubicFunction 0 0)
  have identity : (fun point : ℝ × ℝ => cubicFunction point.1 0 + cubicFunction 0 point.2 - cubicFunction 0 0) =
      (fun point : ℝ × ℝ => cubicFunction point.1 point.2) := by funext point; unfold cubicFunction; ring
  simp only [Pi.add_apply,Function.comp_apply] at combined
  rw [identity] at combined
  refine ⟨(ContinuousLinearMap.toSpanSingleton ℝ (3*(72+point.1)^2)).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ)+
    (ContinuousLinearMap.toSpanSingleton ℝ (3*(54+point.2)^2)).comp
      (ContinuousLinearMap.snd ℝ ℝ ℝ),combined,?_⟩
  intro direction
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

theorem cubic_isolated_coordinates_rational (point : cubicSource)
    (isolated : IsOpen ({point} : Set cubicSource)) :
    (∃ first : ℚ, (first : ℝ)=point.val.1) ∧ (∃ second : ℚ, (second : ℝ)=point.val.2) := by
  obtain ⟨first,first_value⟩ := point.property.1.1
  obtain ⟨second,second_value⟩ := point.property.1.2
  have bounds := cubic_source_bounds point.property
  obtain ⟨derivative,differentiable,formula⟩ := cubic_hasFDerivAt point.val
  obtain ⟨radius,radius_positive,ball⟩ := Metric.isOpen_iff.mp isolated point (by simp)
  have point_eq : (address (1/3) first,address (1/3) second)=point.val := Prod.ext first_value second_value
  have isolated_ball : ∀ other ∈ Classical.cantorLevel cubicFunction
      (cubicFunction (address (1/3) first) (address (1/3) second)),
      dist other (address (1/3) first,address (1/3) second) < radius →
        other = (address (1/3) first,address (1/3) second) := by
    intro other membership close
    have other_mem : other ∈ cubicSource := by
      simpa only [cubicSource,first_value,second_value,
        show cubicFunction point.val.1 point.val.2 = 0 from point.property.2] using membership
    have nearby : (⟨other,other_mem⟩ : cubicSource) ∈ Metric.ball point radius := by
      change dist other point.val < radius
      simpa only [point_eq] using close
    exact (congrArg Subtype.val (Set.mem_singleton_iff.mp (ball nearby))).trans point_eq.symm
  have ratio_eq : 3*(72+point.val.1)^2/(3*(54+point.val.2)^2) = cubicTangent point.val := by
    unfold cubicTangent
    exact mul_div_mul_left _ _ (by norm_num : (3 : ℝ) ≠ 0)
  have rational := Classical.good_slope_isolated_coordinates_rational cubicFunction
    cubicFunction_continuous.continuousOn 15552 15987 8748 9075 cubic_coordinate_bounds
    (by norm_num) (by norm_num) first second (3*(72+point.val.1)^2) (3*(54+point.val.2)^2)
    (by have := bounds.2.1; positivity) (by rw [ratio_eq]; exact cubic_tangent_good point.property)
    derivative (by simpa only [point_eq] using differentiable) formula radius radius_positive isolated_ball
  obtain ⟨⟨rational_first,first_equal⟩,⟨rational_second,second_equal⟩⟩ := rational
  exact ⟨⟨rational_first,first_equal.trans first_value⟩,⟨rational_second,second_equal.trans second_value⟩⟩

theorem cubic_embedding_equation {point : ℝ × ℝ} (membership : point ∈ cubicSource) :
    (cubicEmbedding point).1^3 + (cubicEmbedding point).2^3 = 1 := by
  have equation : cubicFunction point.1 point.2 = 0 := membership.2
  unfold cubicFunction at equation
  change ((54+point.2)/81)^3 + ((72+point.1)/81)^3 = 1
  rw [div_pow,div_pow,← add_div]
  apply (div_eq_iff (by norm_num : (81 : ℝ)^3 ≠ 0)).2
  nlinarith [equation]

theorem cubic_embedding_mem_intersection {point : ℝ × ℝ} (membership : point ∈ cubicSource) :
    cubicEmbedding point ∈ intersection 3 (1/3) := by
  have first := Classical.prefix_cantor_embedding (fun index => decide (index = 0)) 4 membership.1.2
  have second := Classical.prefix_cantor_embedding (fun index => decide (index < 2)) 4 membership.1.1
  have first_prefix : prefixValue (1/3) (fun index => decide (index = 0)) 4 = (54:ℝ)/81 := by
    norm_num [prefixValue, Finset.sum_range_succ]
  have second_prefix : prefixValue (1/3) (fun index => decide (index < 2)) 4 = (72:ℝ)/81 := by
    norm_num [prefixValue, Finset.sum_range_succ]
  rw [first_prefix] at first
  rw [second_prefix] at second
  refine ⟨?_,?_,?_⟩
  · convert first using 1 <;> norm_num [cubicEmbedding] <;> ring
  · convert second using 1 <;> norm_num [cubicEmbedding] <;> ring
  · change (cubicEmbedding point).1 ^ (3 : ℝ) + (cubicEmbedding point).2 ^ (3 : ℝ) = 1
    calc
      _ = (cubicEmbedding point).1 ^ (3 : ℕ) + (cubicEmbedding point).2 ^ (3 : ℕ) :=
        congrArg₂ (fun first second : ℝ => first+second)
          (Real.rpow_ofNat (cubicEmbedding point).1 3)
          (Real.rpow_ofNat (cubicEmbedding point).2 3)
      _ = 1 := cubic_embedding_equation membership

theorem cubic_source_no_isolated (point : cubicSource) : ¬ IsOpen ({point} : Set cubicSource) := by
  intro isolated
  obtain ⟨⟨first,first_equal⟩,⟨second,second_equal⟩⟩ := cubic_isolated_coordinates_rational point isolated
  have bounds := cubic_source_bounds point.property
  apply positive_rational_coordinates_not_on_fermat 3 (by norm_num)
    ((cubicEmbedding point.val).1) ((cubicEmbedding point.val).2)
    (by dsimp [cubicEmbedding]; linarith [bounds.2.1])
    (by dsimp [cubicEmbedding]; linarith [bounds.1.1]) _ _ (cubic_embedding_equation point.property)
  · refine ⟨(54+second)/81, ?_⟩
    push_cast
    simp only [second_equal, cubicEmbedding]
  · refine ⟨(72+first)/81, ?_⟩
    push_cast
    simp only [first_equal, cubicEmbedding]

theorem cubic_source_has_irrational_tangent :
    ∃ point ∈ cubicSource, ∀ rational : ℚ, cubicTangent point ≠ (rational : ℝ) := by
  apply compact_source_has_irrational_tangent cubicSource cubic_source_compact cubic_source_nonempty
    cubic_source_no_isolated cubicTangent
  intro first first_mem second second_mem equality
  have first_bounds := cubic_source_bounds first_mem
  have second_bounds := cubic_source_bounds second_mem
  have tangent_eq (point : ℝ × ℝ) : fermatTangent 3 (cubicEmbedding point) = cubicTangent point := by
    change ((72+point.1)/81)^2/((54+point.2)/81)^2 =
      (72+point.1)^2/(54+point.2)^2
    rw [div_pow,div_pow]
    exact div_div_div_cancel_right₀ (by norm_num : (81 : ℝ)^2 ≠ 0) _ _
  have embedding_eq := fermat_tangent_injective 3 (by norm_num)
    (cubicEmbedding '' cubicSource)
    (by rintro _ ⟨point,member,rfl⟩; have bounds := cubic_source_bounds member
        dsimp [cubicEmbedding]; constructor <;> linarith [bounds.1.1,bounds.2.1])
    (by rintro _ ⟨point,member,rfl⟩; exact cubic_embedding_equation member)
    ⟨first,first_mem,rfl⟩ ⟨second,second_mem,rfl⟩
    (by simpa only [tangent_eq] using equality)
  have first_eq := congrArg Prod.fst embedding_eq
  have second_eq := congrArg Prod.snd embedding_eq
  dsimp [cubicEmbedding] at first_eq second_eq
  apply Prod.ext <;> linarith

end LambdaCantor.Integer
