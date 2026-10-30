import LambdaCantor.Classical.NoIsolation
import LambdaCantor.Integer.GoodSlopePositiveDimension
import LambdaCantor.Integer.IrrationalTangentSelection
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod

noncomputable section
namespace LambdaCantor.Classical
open Last

/-- The derivative ratio in the source coordinates of the actual circle. -/
def cylinderTangent (point : ℝ × ℝ) : ℝ :=
  (6336+point.1)/(9*(566+point.2))

theorem sourceLevel_bounds {point : ℝ × ℝ} (membership : point ∈ sourceLevel) :
    point.1 ∈ Set.Icc (0 : ℝ) 1 ∧ point.2 ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨cantorSet_subset_unitInterval (by norm_num) (by norm_num) membership.1.1,
    cantorSet_subset_unitInterval (by norm_num) (by norm_num) membership.1.2⟩

theorem cylinder_tangent_good {point : ℝ × ℝ} (membership : point ∈ sourceLevel) :
    Integer.GoodSlope (cylinderTangent point) := by
  have bounds := sourceLevel_bounds membership
  have ratio := cylinder_ratio_bounds point.1 point.2 bounds.1 bounds.2
  exact Integer.goodSlope_of_classical_band ratio.1 ratio.2

theorem sourceLevel_not_isolated (point : sourceLevel) :
    ¬ IsOpen ({point} : Set sourceLevel) := by
  intro isolated
  obtain ⟨radius,positive,ball⟩ := Metric.isOpen_iff.mp isolated point (by simp)
  apply sourceLevel_no_isolated point.val point.property radius positive
  intro other membership close
  have nearby : (⟨other,membership⟩ : sourceLevel) ∈ Metric.ball point radius := close
  exact congrArg Subtype.val (Set.mem_singleton_iff.mp (ball nearby))

theorem cylinder_tangent_injective : Set.InjOn cylinderTangent sourceLevel := by
  intro first first_mem second second_mem equality
  have first_bounds := sourceLevel_bounds first_mem
  have second_bounds := sourceLevel_bounds second_mem
  have first_denominator : 9*(566+first.2) ≠ 0 := by
    have := first_bounds.2.1
    positivity
  have second_denominator : 9*(566+second.2) ≠ 0 := by
    have := second_bounds.2.1
    positivity
  have first_identity : 6336+first.1 = cylinderTangent first*(9*(566+first.2)) :=
    (div_eq_iff first_denominator).mp rfl
  have second_identity : 6336+second.1 = cylinderTangent first*(9*(566+second.2)) :=
    (div_eq_iff second_denominator).mp equality.symm
  have factor_identity :
      (81*(cylinderTangent first)^2+9)*(566+first.2)^2 =
        (81*(cylinderTangent first)^2+9)*(566+second.2)^2 := by
    calc
      _ = cylinderPolynomial first.1 first.2 := by
        rw [cylinderPolynomial,first_identity]
        ring
      _ = 3^16 := first_mem.2
      _ = cylinderPolynomial second.1 second.2 := second_mem.2.symm
      _ = _ := by
        rw [cylinderPolynomial,second_identity]
        ring
  have squares := mul_left_cancel₀
    (show 81*(cylinderTangent first)^2+9 ≠ 0 by positivity) factor_identity
  have second_equal : first.2 = second.2 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp squares with equal | opposite
    · linarith
    · linarith [first_bounds.2.1,second_bounds.2.1]
  apply Prod.ext
  · rw [second_equal] at first_identity
    linarith [first_identity,second_identity]
  · exact second_equal

theorem sourceLevel_has_irrational_tangent :
    ∃ point ∈ sourceLevel, ∀ rational : ℚ, cylinderTangent point ≠ (rational : ℝ) :=
  Integer.compact_source_has_irrational_tangent sourceLevel sourceLevel_compact
    sourceLevel_nonempty sourceLevel_not_isolated cylinderTangent cylinder_tangent_injective

/-- The actual polynomial has a strict derivative, rather than merely an
ordinary derivative assumed to control Lipschitz remainders. -/
theorem cylinder_hasStrictFDerivAt (point : ℝ × ℝ) :
    ∃ derivative : (ℝ × ℝ) →L[ℝ] ℝ,
      HasStrictFDerivAt (fun value : ℝ × ℝ => cylinderPolynomial value.1 value.2) derivative point ∧
      ∀ direction, derivative direction =
        2*(6336+point.1)*direction.1+18*(566+point.2)*direction.2 := by
  have first := ((hasStrictFDerivAt_fst :
    HasStrictFDerivAt (fun value : ℝ × ℝ => value.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) point).const_add (6336 : ℝ)).pow 2
  have second := (((hasStrictFDerivAt_snd :
    HasStrictFDerivAt (fun value : ℝ × ℝ => value.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) point).const_add (566 : ℝ)).pow 2).const_mul 9
  refine ⟨_,first.add second,?_⟩
  intro direction
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul,nsmul_eq_mul,Nat.cast_ofNat,Nat.reduceSub,pow_one]
  change 2*(6336+point.1)*direction.1+9*(2*(566+point.2)*direction.2) = _
  ring

theorem classical_source_positive_dimension : 0 < dimH sourceLevel := by
  obtain ⟨point,membership,irrational⟩ := sourceLevel_has_irrational_tangent
  have bounds := sourceLevel_bounds membership
  have vertical_positive : 0 < 18*(566+point.2) := by
    have := bounds.2.1
    positivity
  have tangent_identity : 2*(6336+point.1)/(18*(566+point.2)) = cylinderTangent point := by
    have denominator_nonzero : 566+point.2 ≠ 0 := by
      have := bounds.2.1
      positivity
    unfold cylinderTangent
    field_simp [denominator_nonzero]
    <;> ring
  obtain ⟨derivative,strict,formula⟩ := cylinder_hasStrictFDerivAt point
  have level_identity : {value : ℝ × ℝ | value ∈ cantorDust (1/3) ∧
      cylinderPolynomial value.1 value.2 = 3^16} = sourceLevel := by
    rfl
  have positive := Integer.good_slope_positive_dimension_of_derivative
    (fun value : ℝ × ℝ => cylinderPolynomial value.1 value.2) (3^16)
    (2*(6336+point.1)) (18*(566+point.2)) vertical_positive
    (by rw [tangent_identity]; exact cylinder_tangent_good membership)
    (by rw [tangent_identity]; exact irrational)
    ⟨point,by rw [level_identity]; exact membership⟩
    (Integer.nonisolated_source_eq level_identity.symm ⟨point,membership⟩
      (sourceLevel_not_isolated ⟨point,membership⟩))
    derivative strict formula
  rwa [level_identity] at positive

theorem cylinderMap_antilipschitz : AntilipschitzWith (3^8) cylinderMap := by
  apply AntilipschitzWith.of_le_mul_dist
  intro first second
  change dist first second ≤ (3 : ℝ)^8*dist (cylinderMap first) (cylinderMap second)
  have first_coordinate : |(cylinderMap first).1-(cylinderMap second).1| ≤
      dist (cylinderMap first) (cylinderMap second) := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_left _ _
  have second_coordinate : |(cylinderMap first).2-(cylinderMap second).2| ≤
      dist (cylinderMap first) (cylinderMap second) := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_right _ _
  have first_identity : (cylinderMap first).1-(cylinderMap second).1 =
      (first.2-second.2)/3^7 := by unfold cylinderMap; ring
  have second_identity : (cylinderMap first).2-(cylinderMap second).2 =
      (first.1-second.1)/3^8 := by unfold cylinderMap; ring
  rw [first_identity,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<3^7)] at first_coordinate
  rw [second_identity,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<3^8)] at second_coordinate
  have horizontal_bound := (div_le_iff₀ (by norm_num : (0 : ℝ)<3^7)).mp first_coordinate
  have vertical_bound := (div_le_iff₀ (by norm_num : (0 : ℝ)<3^8)).mp second_coordinate
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
  apply max_le
  · simpa only [mul_comm] using vertical_bound
  · have nonnegative := dist_nonneg (x := cylinderMap first) (y := cylinderMap second)
    norm_num at horizontal_bound ⊢
    nlinarith

/-- The purely analytic Section 2 positivity conclusion for the actual circle.
No quantitative weighted-return certificate is imported or assumed. -/
theorem classical_circle_positive_dimension : 0 < dimH (intersection 2 (1/3)) := by
  apply classical_source_positive_dimension.trans_le
  apply (cylinderMap_antilipschitz.le_dimH_image sourceLevel).trans
  exact dimH_mono source_subset_circle

end LambdaCantor.Classical
