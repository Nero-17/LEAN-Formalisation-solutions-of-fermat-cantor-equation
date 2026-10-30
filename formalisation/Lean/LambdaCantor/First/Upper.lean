import LambdaCantor.First.GraphDimension
import LambdaCantor.First.CurveExceptional

/-! Assembly of Section 2's universal dimension upper bound. The only
external input is the explicitly registered homogeneous measure theorem.
All geometric, counting, exceptional-tangent and local-to-global steps are
provided by the imported proof modules. -/

noncomputable section
namespace LambdaCantor.First

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal
open PrefixSlopes

def regularCurveIntersection (exponent ratio : ℝ) : Set (ℝ × ℝ) :=
  intersection exponent ratio ∩ curvePoint exponent ''
    (Set.Ioo (0 : ℝ) 1 \ curveSlope exponent ⁻¹'
      ExceptionalSlopes.frequentCollisionSlopes (planarTranslation ratio))

theorem regularCurveIntersection_bound {exponent ratio : ℝ}
    (hexponent : 1 < exponent) (hratio : 0 < ratio) (hhalf : ratio < 1 / 2)
    (targetExponent : ℝ≥0) (htarget : dimensionUpperBound ratio < (targetExponent : ℝ)) :
    dimH (regularCurveIntersection exponent ratio) ≤ targetExponent := by
  apply dimH_le_of_local_bounds
  rintro point ⟨hintersection, x, hx, rfl⟩
  obtain ⟨block, hblock, hbound⟩ :=
    exists_block_for_flat_target hratio hhalf hx.2 targetExponent htarget
  have hcontinuous : ContinuousAt (curveSlope exponent) x := by
    obtain ⟨derivative, _, hderivative⟩ := curveSlope_hasDerivAt_negative hexponent hx.1
    exact hderivative.continuousAt
  have hnear : (Set.Ioo (0 : ℝ) 1 ∩ curveSlope exponent ⁻¹'
      Metric.ball (curveSlope exponent x) (ratio ^ block)) ∈ 𝓝 x :=
    inter_mem (isOpen_Ioo.mem_nhds hx.1)
      (hcontinuous.preimage_mem_nhds (Metric.ball_mem_nhds _ (pow_pos hratio block)))
  obtain ⟨radius, hradius, hsubset⟩ := Metric.mem_nhds_iff.1 hnear
  refine ⟨regularCurveIntersection exponent ratio ∩
    Prod.fst ⁻¹' Metric.ball x radius, ?_, ?_⟩
  · apply inter_mem self_mem_nhdsWithin
    apply mem_nhdsWithin_of_mem_nhds
    exact continuous_fst.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hradius)
  · apply hbound
    · intro point hpoint
      exact ⟨hpoint.1.1.1, hpoint.1.1.2.1⟩
    · rintro left ⟨⟨hleft, leftX, hleftX, rfl⟩, hleftBall⟩
        right ⟨⟨hright, rightX, hrightX, rfl⟩, hrightBall⟩
      have hderivative : ∀ value ∈ Metric.ball x radius,
          HasDerivWithinAt (fun value : ℝ => (1 - value ^ exponent) ^ exponent⁻¹)
            (curveSlope exponent value) (Metric.ball x radius) value := by
        intro value hvalue
        exact (hasDerivAt_curveHeight (lt_trans zero_lt_one hexponent)
          (hsubset hvalue).1).hasDerivWithinAt
      have hclose : ∀ value ∈ Metric.ball x radius,
          |curveSlope exponent value - curveSlope exponent x| ≤ ratio ^ block := by
        intro value hvalue
        have h := (hsubset hvalue).2
        have hlt : |curveSlope exponent value - curveSlope exponent x| < ratio ^ block := by
          simpa only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] using h
        exact hlt.le
      have hmean := graph_strip_of_derivative_close (convex_ball x radius)
        hderivative hclose hrightBall hleftBall
      dsimp only [curvePoint] at hmean
      change |((1 - leftX ^ exponent) ^ exponent⁻¹ -
        (1 - rightX ^ exponent) ^ exponent⁻¹) -
        curveSlope exponent x * (leftX - rightX)| ≤ ratio ^ block * |leftX - rightX|
      convert hmean using 1 <;> congr 1 <;> ring

theorem intersection_bound_above {exponent ratio : ℝ}
    (hexponent : 1 < exponent) (hratio : 0 < ratio) (hhalf : ratio < 1 / 2)
    (targetExponent : ℝ≥0) (htarget : dimensionUpperBound ratio < (targetExponent : ℝ)) :
    dimH (intersection exponent ratio) ≤ targetExponent := by
  have hzero := exceptional_power_arc_dimension_zero hexponent
    (cantor_projection_collision_slopes_dimension_zero hratio hhalf)
  have hcover : intersection exponent ratio ⊆
      ({curvePoint exponent 0} ∪ {curvePoint exponent 1}) ∪
        curvePoint exponent '' (Set.Ioo (0 : ℝ) 1 ∩ curveSlope exponent ⁻¹'
          ExceptionalSlopes.frequentCollisionSlopes (planarTranslation ratio)) ∪
        regularCurveIntersection exponent ratio := by
    intro point hpoint
    rcases intersection_subset_curve (lt_trans zero_lt_one hexponent) hratio.le
      (by linarith : ratio < 1) hpoint with haxis | ⟨x, hx, hequal⟩
    · exact Or.inl (Or.inl haxis)
    · by_cases hexceptional : curveSlope exponent x ∈
          ExceptionalSlopes.frequentCollisionSlopes (planarTranslation ratio)
      · exact Or.inl (Or.inr ⟨x, ⟨hx, hexceptional⟩, hequal⟩)
      · exact Or.inr ⟨hpoint, x, ⟨hx, hexceptional⟩, hequal⟩
  apply (dimH_mono hcover).trans
  rw [dimH_union, dimH_union, hzero]
  apply max_le
  · simp only [dimH_union, dimH_singleton, max_self]
    exact zero_le
  · exact regularCurveIntersection_bound hexponent hratio hhalf targetExponent htarget

/-- Theorem dimension-upper from the frozen manuscript. -/
theorem dimension_upper {exponent ratio : ℝ} (hexponent : 1 < exponent)
    (hratio : 0 < ratio) (hhalf : ratio ≤ 1 / 2) :
    dimH (intersection exponent ratio) ≤ ENNReal.ofReal (dimensionUpperBound ratio) := by
  rcases lt_or_eq_of_le hhalf with hstrict | rfl
  · apply ENNReal.le_of_forall_pos_le_add
    intro epsilon hpositive _
    let baseExponent : ℝ≥0 := ⟨dimensionUpperBound ratio, dimensionUpperBound_nonneg ratio⟩
    let targetExponent : ℝ≥0 := baseExponent + epsilon
    have htarget : dimensionUpperBound ratio < (targetExponent : ℝ) := by
      change dimensionUpperBound ratio < dimensionUpperBound ratio + (epsilon : ℝ)
      exact lt_add_of_pos_right _ hpositive
    have hbound := intersection_bound_above hexponent hratio hstrict targetExponent htarget
    have hcast : (baseExponent : ℝ≥0∞) = ENNReal.ofReal (baseExponent : ℝ) :=
      ENNReal.coe_nnreal_eq baseExponent
    simp only [targetExponent, ENNReal.coe_add] at hbound
    rw [hcast] at hbound
    exact hbound
  · exact dimension_upper_half hexponent

/-- Corollary first-lower from the frozen manuscript. -/
theorem first_lower {exponent : ℝ} (hexponent : 1 < exponent) :
    1 / 4 ≤ firstTransition exponent := by
  apply first_lower_of_dimension_upper hexponent
  intro ratio hratio hhalf
  exact dimension_upper hexponent hratio hhalf

end LambdaCantor.First

#print axioms LambdaCantor.First.dimension_upper
#print axioms LambdaCantor.First.first_lower
