import LambdaCantor.AE.DimensionMeasurabilityTheorem
import LambdaCantor.AE.KernelDensityBridge

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace LambdaCantor.AE

/-- The actual dimension-equality set restricted to a compact real parameter
band is Borel in the ambient real line. -/
theorem measurableSet_dimension_equality_closed_band {exponent lower upper : ℝ}
    (exponent_positive : 0 < exponent) (lower_nonnegative : 0 ≤ lower)
    (upper_less_one : upper < 1) (ordered : lower ≤ upper) :
    MeasurableSet {ratio : ℝ | ratio ∈ Icc lower upper ∧
      dimH (intersection exponent ratio) = ENNReal.ofReal (expectedDimension ratio)} := by
  have measurable := measurableSet_Icc.subtype_image
    (measurableSet_dimension_equality_band exponent_positive lower_nonnegative upper_less_one ordered)
  convert measurable using 1
  ext ratio
  constructor
  · intro membership
    exact ⟨⟨ratio, membership.1⟩, membership.2, rfl⟩
  · rintro ⟨parameter, equality, rfl⟩
    exact ⟨parameter.property, equality⟩

/-- Terminal implication for the actual dimension equality. This theorem proves
the density contradiction and Borel obligations internally; the local kernel
mass and L2 estimates remain explicit until the centered construction supplies them. -/
theorem ae_dimension_equality_of_local_kernel_estimates {exponent lower upper : ℝ}
    (exponent_positive : 0 < exponent) (lower_nonnegative : 0 ≤ lower)
    (upper_less_one : upper < 1) (ordered : lower ≤ upper)
    (local_kernels : ∀ᵐ centre : ℝ, centre ∈ Ioo lower upper →
      ∃ (radii : ℕ → ℝ) (constant : ℝ) (density : ℕ → Lp ℝ 2 volume),
        0 < constant ∧ (∀ depth, 0 < radii depth) ∧ Tendsto radii atTop (𝓝[>] 0) ∧
        ∀ᶠ depth in atTop,
          (1/2 ≤ ∫ point in
            {ratio : ℝ | ratio ∈ Icc lower upper ∧
              dimH (intersection exponent ratio) = ENNReal.ofReal (expectedDimension ratio)} ∩
                closedBall centre (radii depth), density depth point) ∧
          ‖density depth‖^2 ≤ constant/radii depth) :
    ∀ᵐ centre : ℝ, centre ∈ Ioo lower upper →
      dimH (intersection exponent centre) = ENNReal.ofReal (expectedDimension centre) := by
  have terminal := ae_mem_of_local_kernel_estimates
    {ratio : ℝ | ratio ∈ Icc lower upper ∧
      dimH (intersection exponent ratio) = ENNReal.ofReal (expectedDimension ratio)}
    (Ioo lower upper)
    (measurableSet_dimension_equality_closed_band exponent_positive lower_nonnegative upper_less_one ordered)
    local_kernels
  filter_upwards [terminal] with centre membership
  intro centre_inside
  exact (membership centre_inside).2

end LambdaCantor.AE
