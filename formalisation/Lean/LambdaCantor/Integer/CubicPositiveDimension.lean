import LambdaCantor.Integer.CubicSource
import LambdaCantor.Integer.GoodSlopePositiveDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic.FunProp

noncomputable section
namespace LambdaCantor.Integer
open Last

theorem cubic_source_positive_dimension : 0 < dimH cubicSource := by
  obtain ⟨point,membership,irrational⟩ := cubic_source_has_irrational_tangent
  have bounds := cubic_source_bounds membership
  have denominator_positive : 0 < 6*(54+point.2)^2 := by
    have := bounds.2.1
    positivity
  let normalized : (ℝ × ℝ) → ℝ := fun value => (1/(6*(54+point.2)^2))*cubicFunction value.1 value.2
  have source_eq : {value : ℝ × ℝ | value ∈ cantorDust (1/3) ∧ normalized value = 0} = cubicSource := by
    ext value
    simp only [normalized,mul_eq_zero,one_div_ne_zero (ne_of_gt denominator_positive),false_or,
      cubicSource,Classical.cantorLevel,Set.mem_inter_iff,Set.mem_setOf_eq,cantorDust]
  obtain ⟨derivative,differentiable,formula⟩ := cubic_hasFDerivAt point
  have smooth : ContDiff ℝ 1 (fun value : ℝ × ℝ => cubicFunction value.1 value.2) := by
    unfold cubicFunction
    fun_prop
  have strict := smooth.contDiffAt.hasStrictFDerivAt' differentiable (by norm_num)
  have normalized_derivative : HasStrictFDerivAt normalized (goodSlopeLinear (cubicTangent point)) point := by
    have scaled := strict.const_smul (1/(6*(54+point.2)^2))
    have linear_eq : (1/(6*(54+point.2)^2)) • derivative = goodSlopeLinear (cubicTangent point) := by
      apply ContinuousLinearMap.ext
      intro direction
      simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,formula,goodSlopeLinear_apply,cubicTangent]
      have base_nonzero : 54+point.2 ≠ 0 := by linarith [bounds.2.1]
      field_simp [base_nonzero]
      <;> ring
    rw [linear_eq] at scaled
    have scaled_little := HasFDerivAtFilter.isLittleOTVS scaled
    apply HasFDerivAtFilter.of_isLittleOTVS
    have product_topology :
        (inferInstance : PseudoMetricSpace (ℝ × ℝ)).toUniformSpace.toTopologicalSpace =
          (instTopologicalSpaceProd : TopologicalSpace (ℝ × ℝ)) := by
      with_reducible_and_instances exact toTopologicalSpace_prod
    simpa only [product_topology,normalized,Pi.smul_apply,smul_eq_mul] using scaled_little
  have normalized_positive : 0 < dimH {value : ℝ × ℝ | value ∈ cantorDust (1/3) ∧ normalized value = 0} := by
    apply good_slope_positive_dimension (cubicTangent point) (cubic_tangent_good membership) irrational
      normalized 0 ⟨point,by rw [source_eq]; exact membership⟩ _ normalized_derivative
    exact nonisolated_source_eq source_eq.symm ⟨point,membership⟩
      (cubic_source_no_isolated ⟨point,membership⟩)
  rwa [source_eq] at normalized_positive

theorem cubicEmbedding_antilipschitz : AntilipschitzWith 81 cubicEmbedding := by
  apply AntilipschitzWith.of_le_mul_dist
  intro first second
  change dist first second ≤ (81:ℝ)*dist (cubicEmbedding first) (cubicEmbedding second)
  rw [Prod.dist_eq,Prod.dist_eq,Real.dist_eq,Real.dist_eq,Real.dist_eq,Real.dist_eq]
  have first_eq : (cubicEmbedding first).1-(cubicEmbedding second).1 = (first.2-second.2)/81 := by
    unfold cubicEmbedding; ring
  have second_eq : (cubicEmbedding first).2-(cubicEmbedding second).2 = (first.1-second.1)/81 := by
    unfold cubicEmbedding; ring
  rw [first_eq,second_eq,abs_div,abs_div]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<81)]
  have first_bound := le_max_left (|first.2-second.2|/81) (|first.1-second.1|/81)
  have second_bound := le_max_right (|first.2-second.2|/81) (|first.1-second.1|/81)
  apply max_le <;> linarith

/-- The concrete direct cubic source gives positive Hausdorff dimension for
the actual middle-thirds Fermat intersection, without a source existence or
perfectness premise. -/
theorem cubic_intersection_positive_dimension : 0 < dimH (intersection 3 (1/3)) := by
  apply cubic_source_positive_dimension.trans_le
  apply (cubicEmbedding_antilipschitz.le_dimH_image cubicSource).trans
  apply dimH_mono
  rintro point ⟨tail,membership,rfl⟩
  exact cubic_embedding_mem_intersection membership

end LambdaCantor.Integer
