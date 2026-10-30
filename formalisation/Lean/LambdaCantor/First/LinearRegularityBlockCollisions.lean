import LambdaCantor.First.LinearRegularityNondegenerate
import LambdaCantor.First.LinearRegularityCollisions

noncomputable section
open scoped BigOperators
namespace LambdaCantor.First.LinearRegularity

theorem denseBlockTranslation_affine (blockLength : ℕ) (ratio slope : ℝ) (word : DenseBlock blockLength) :
    denseBlockTranslation blockLength (ratio, slope) word =
      slope * (denseBlockTranslation blockLength (ratio, 1) word -
        denseBlockTranslation blockLength (ratio, 0) word) + denseBlockTranslation blockLength (ratio, 0) word := by
  unfold denseBlockTranslation
  simp only [one_mul, zero_mul, zero_add]
  simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

theorem denseBlockTranslation_ratio_smooth (blockLength : ℕ) (slope ratio : ℝ) (word : DenseBlock blockLength) :
    ContDiffAt ℝ 1 (fun parameter => denseBlockTranslation blockLength (parameter, slope) word) ratio := by
  have h := denseBlockTranslation_analytic blockLength word Set.univ (ratio, slope) (Set.mem_univ _)
  have hpair : AnalyticAt ℝ (fun parameter : ℝ => (parameter, slope)) ratio :=
    AnalyticAt.prod analyticAt_id analyticAt_const
  exact (h.comp_of_eq hpair rfl).contDiffAt

/-- The affine slope coefficients for two distinct block symbols cannot
vanish together at any contraction below one half. -/
theorem denseBlockTranslation_no_common {ratio : ℝ} (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (blockLength : ℕ) (hblock : 0 < blockLength) (left right : DenseBlock blockLength) (hne : left ≠ right) :
    (denseBlockTranslation blockLength (ratio, 1) left - denseBlockTranslation blockLength (ratio, 0) left) -
      (denseBlockTranslation blockLength (ratio, 1) right - denseBlockTranslation blockLength (ratio, 0) right) ≠ 0 ∨
    denseBlockTranslation blockLength (ratio, 0) left - denseBlockTranslation blockLength (ratio, 0) right ≠ 0 := by
  by_contra h
  push_neg at h
  rcases h with ⟨hslopeZero, hinterceptZero⟩
  have hslopeEqual := sub_eq_zero.mp hslopeZero
  have hinterceptEqual := sub_eq_zero.mp hinterceptZero
  obtain ⟨slope, hslope, hdifferent⟩ := denseBlock_series_nondegenerate hpositive hhalf
    (by norm_num : (0 : ℝ) < 1) blockLength hblock (fun _ => left) (fun _ => right)
      (by intro hequal; exact hne (congrFun hequal 0))
  apply hdifferent
  unfold affineAddress
  apply tsum_congr
  intro index
  congr 1
  rw [denseBlockTranslation_affine blockLength ratio slope left,
    denseBlockTranslation_affine blockLength ratio slope right,
    hslopeEqual, hinterceptEqual]

/-- Each pairwise dense-translation collision set has dimension at most one. -/
theorem dimH_denseBlock_collision (blockLength : ℕ) (hblock : 0 < blockLength)
    (left right : DenseBlock blockLength) (hne : left ≠ right) :
    dimH {parameter : ℝ × ℝ | parameter.1 ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧
      denseBlockTranslation blockLength parameter left = denseBlockTranslation blockLength parameter right} ≤ 1 := by
  have heq : {parameter : ℝ × ℝ | parameter.1 ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧
      denseBlockTranslation blockLength parameter left = denseBlockTranslation blockLength parameter right} =
      {parameter : ℝ × ℝ | parameter.1 ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧
        parameter.2 * ((denseBlockTranslation blockLength (parameter.1, 1) left -
          denseBlockTranslation blockLength (parameter.1, 0) left) -
          (denseBlockTranslation blockLength (parameter.1, 1) right -
          denseBlockTranslation blockLength (parameter.1, 0) right)) +
        (denseBlockTranslation blockLength (parameter.1, 0) left -
          denseBlockTranslation blockLength (parameter.1, 0) right) = 0} := by
    ext parameter
    simp only [Set.mem_setOf_eq]
    apply and_congr_right
    intro hband
    have hleft := denseBlockTranslation_affine blockLength parameter.1 parameter.2 left
    have hright := denseBlockTranslation_affine blockLength parameter.1 parameter.2 right
    change denseBlockTranslation blockLength (parameter.1, parameter.2) left =
      denseBlockTranslation blockLength (parameter.1, parameter.2) right ↔ _
    constructor <;> intro h <;> nlinarith [hleft, hright]
  rw [heq]
  exact dimH_affine_slope_collision_le_one
    (domain := Set.Ioo (0 : ℝ) (1 / 2))
    (slopeCoefficient := fun ratio =>
      (denseBlockTranslation blockLength (ratio, 1) left - denseBlockTranslation blockLength (ratio, 0) left) -
        (denseBlockTranslation blockLength (ratio, 1) right - denseBlockTranslation blockLength (ratio, 0) right))
    (intercept := fun ratio =>
      denseBlockTranslation blockLength (ratio, 0) left - denseBlockTranslation blockLength (ratio, 0) right)
    (hslope := by
      intro ratio hratio
      exact ((denseBlockTranslation_ratio_smooth blockLength 1 ratio left).sub
        (denseBlockTranslation_ratio_smooth blockLength 0 ratio left)).sub
        ((denseBlockTranslation_ratio_smooth blockLength 1 ratio right).sub
          (denseBlockTranslation_ratio_smooth blockLength 0 ratio right)))
    (hintercept := by
      intro ratio hratio
      exact (denseBlockTranslation_ratio_smooth blockLength 0 ratio left).sub
        (denseBlockTranslation_ratio_smooth blockLength 0 ratio right))
    (hnocommon := by
      intro ratio hratio
      exact denseBlockTranslation_no_common hratio.1 hratio.2 blockLength hblock left right hne)

end LambdaCantor.First.LinearRegularity
