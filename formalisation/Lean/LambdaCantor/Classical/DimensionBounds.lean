import LambdaCantor.Classical.PositiveDimension
import LambdaCantor.First.Upper

noncomputable section
namespace LambdaCantor.Classical

theorem classical_circle_dimension_upper :
    dimH (intersection 2 (1/3)) ≤ ENNReal.ofReal (2*Real.log 2/Real.log 3-1) := by
  have logarithm_positive : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have logarithm_bound : Real.log 3 ≤ 2*Real.log 2 := by
    rw [← First.log_four]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have bound_nonnegative : 0 ≤ 2*Real.log 2/Real.log 3-1 := by
    have divided : (1 : ℝ) ≤ 2*Real.log 2/Real.log 3 :=
      (le_div_iff₀ logarithm_positive).mpr (by simpa using logarithm_bound)
    linarith
  have specialization : First.dimensionUpperBound (1/3) = 2*Real.log 2/Real.log 3-1 := by
    unfold First.dimensionUpperBound
    rw [show (1 : ℝ)/(1/3) = 3 by norm_num, max_eq_left bound_nonnegative]
  rw [← specialization]
  exact First.dimension_upper (by norm_num) (by norm_num) (by norm_num)

/-- The exact pair of bounds in manuscript Theorem circle-quantitative. -/
theorem classical_circle_dimension_bounds :
    0 < dimH (intersection 2 (1/3)) ∧
      dimH (intersection 2 (1/3)) ≤ ENNReal.ofReal (2*Real.log 2/Real.log 3-1) :=
  ⟨classical_circle_positive_dimension, classical_circle_dimension_upper⟩

end LambdaCantor.Classical

#print axioms LambdaCantor.Classical.classical_circle_dimension_bounds
