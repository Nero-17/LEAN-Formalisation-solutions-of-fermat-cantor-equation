import LambdaCantor.First.RootFibreTopology
import LambdaCantor.First.Onset

noncomputable section
open MeasureTheory Filter

namespace LambdaCantor.First.Roots

theorem expectedDimension_positive {ratio : ℝ}
    (above_quarter : 1 / 4 < ratio) (below_half : ratio < 1 / 2) :
    0 < expectedDimension ratio := by
  have positive : 0 < ratio := by linarith
  have reciprocal_above_one : 1 < 1 / ratio :=
    (lt_div_iff₀ positive).mpr (by linarith)
  have reciprocal_below_four : 1 / ratio < (2 : ℝ) ^ 2 :=
    (div_lt_iff₀ positive).mpr (by nlinarith)
  have logarithm_positive := Real.log_pos reciprocal_above_one
  have logarithm_bound := Real.log_lt_log (div_pos (by norm_num) positive)
    reciprocal_below_four
  rw [Real.log_pow] at logarithm_bound
  have quotient_above_one : 1 < 2 * Real.log 2 / Real.log (1 / ratio) :=
    (lt_div_iff₀ logarithm_positive).mpr (by simpa using logarithm_bound)
  unfold expectedDimension
  linarith

/-- A proved root-fibre conclusion is carried by positive-dimensional
parameters in the actual closed parameter band. -/
theorem rootFibreConclusion_ae_positive_band {exponent : ℝ}
    (data : RootFibreData exponent) (conclusion : RootFibreConclusion data) :
    ∀ᵐ ratio ∂rootLaw data.root,
      ratio ∈ Set.Icc data.lower data.upper ∧ 0 < dimH (intersection exponent ratio) := by
  letI := rootFibreData_rootLaw_probability data
  have in_band : ∀ᵐ ratio ∂rootLaw data.root, ratio ∈ Set.Icc data.lower data.upper := by
    apply (ae_mem_iff_measure_eq measurableSet_Icc.nullMeasurableSet).mpr
    simpa using rootFibreData_rootLaw_parameter_band data
  filter_upwards [in_band, conclusion.2] with ratio parameter_band dimension
  refine ⟨parameter_band, ?_⟩
  rw [dimension]
  exact ENNReal.ofReal_pos.mpr (expectedDimension_positive
    (data.lower_gt_quarter.trans_le parameter_band.1)
    (parameter_band.2.trans_lt data.upper_lt_half))

theorem rootFibreConclusion_exists_positive_band {exponent : ℝ}
    (data : RootFibreData exponent) (conclusion : RootFibreConclusion data) :
    ∃ ratio ∈ Set.Icc data.lower data.upper, 0 < dimH (intersection exponent ratio) := by
  letI := rootFibreData_rootLaw_probability data
  exact (rootFibreConclusion_ae_positive_band data conclusion).exists

/-- Outer Lebesgue measure suffices, so this deduction does not impose a
separate measurability premise on the dimension-positive parameter set. -/
theorem rootFibreConclusion_positive_volume_band {exponent : ℝ}
    (data : RootFibreData exponent) (conclusion : RootFibreConclusion data) :
    0 < volume {ratio : ℝ | ratio ∈ Set.Icc data.lower data.upper ∧
      0 < dimH (intersection exponent ratio)} := by
  letI := rootFibreData_rootLaw_probability data
  apply pos_iff_ne_zero.mpr
  intro zero
  have zero_root := conclusion.1 zero
  have almost_not := measure_eq_zero_iff_ae_notMem.mp zero_root
  obtain ⟨ratio, member, not_member⟩ :=
    ((rootFibreConclusion_ae_positive_band data conclusion).and almost_not).exists
  exact not_member member

theorem rootFibreConclusion_firstTransition_le_upper {exponent : ℝ}
    (data : RootFibreData exponent) (conclusion : RootFibreConclusion data) :
    firstTransition exponent ≤ data.upper := by
  obtain ⟨ratio, parameter_band, dimension⟩ :=
    rootFibreConclusion_exists_positive_band data conclusion
  have admissible : ratio ∈ Set.Ioc (0 : ℝ) (1 / 2) :=
    ⟨by linarith [data.lower_gt_quarter, parameter_band.1],
      (parameter_band.2.trans_lt data.upper_lt_half).le⟩
  exact (firstTransition_le_of_positive admissible dimension).trans parameter_band.2

end LambdaCantor.First.Roots
