import LambdaCantor.Last.AnalyticIsolatedActualChildData
import LambdaCantor.Last.AnalyticIsolatedActualError
import LambdaCantor.Last.AnalyticIsolatedSmallHull
import LambdaCantor.Last.AnalyticIsolatedAffineHulls
import LambdaCantor.Last.AnalyticIsolatedPhaseTolerance

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

theorem actual_open_phase_cylinder_exclusive {ratio slope : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2)
    (function : (ℝ × ℝ) → ℝ) (word : List (Bool × Bool)) (point : ℝ × ℝ)
    {bound : ℝ≥0} (tolerance : ActualPhaseTolerance ratio slope bound)
    (error_lipschitz : LipschitzOnWith bound
      (fun value => function value-positiveLinearContinuous slope value) (wordCylinder ratio word))
    (normalized_error : ∀ value ∈ cantorDust ratio,
      |normalizedActualFunction function ratio word value-positiveLinearContinuous slope value| ≤ bound)
    (singleton : ∀ other : ℝ × ℝ, other ∈ cantorDust ratio → function other = function point →
      other ∈ wordCylinder ratio word → other = point)
    (digit : Bool × Bool) (tail : ℝ × ℝ) (tail_mem : tail ∈ cantorDust ratio)
    (representation : wordMap ratio word (wordMap ratio [digit] tail) = point) :
    ApproxAffineExclusiveRegion ratio slope
      (positiveLinearContinuous slope (wordMap ratio [digit] tail)) (2*(bound : ℝ)) digit := by
  have less_one : ratio < 1 := by linarith
  have slope_lower : 1 ≤ slope := by
    rcases tolerance.2.2.2.2 with small | mixed
    · exact small.1.1
    · exact mixed.1.1.le
  let lower := fun child : Bool × Bool => normalizedActualFunction function ratio word (wordMap ratio [child] 0)
  let upper := fun child : Bool × Bool => normalizedActualFunction function ratio word (wordMap ratio [child] (1,1))
  let actualLevel := normalizedActualFunction function ratio word (wordMap ratio [digit] tail)
  have child_data := actual_cylinder_unique_child_hulls positive less_half slope_lower function word point
    tolerance.1.le error_lipschitz tolerance.2.1 tolerance.2.2.1 singleton digit tail tail_mem representation
  have zero_mem : (0 : ℝ × ℝ) ∈ cantorDust ratio := ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩
  have one_mem : ((1,1) : ℝ × ℝ) ∈ cantorDust ratio :=
    ⟨one_mem_cantorSet positive.le less_one, one_mem_cantorSet positive.le less_one⟩
  have lower_close : ∀ child, |lower child-affineChildOffset ratio slope child| ≤ (bound : ℝ) := by
    intro child
    rw [← (affine_child_endpoint_values ratio slope child).1]
    exact normalized_error _ (wordMap_mem_dust positive.le less_one [child] zero_mem)
  have upper_close : ∀ child,
      |upper child-(affineChildOffset ratio slope child+ratio*(1+slope))| ≤ (bound : ℝ) := by
    intro child
    rw [← (affine_child_endpoint_values ratio slope child).2]
    exact normalized_error _ (wordMap_mem_dust positive.le less_one [child] one_mem)
  have level_close : |positiveLinearContinuous slope (wordMap ratio [digit] tail)-actualLevel| ≤ (bound : ℝ) := by
    simpa [actualLevel, abs_sub_comm] using normalized_error _
      (wordMap_mem_dust positive.le less_one [digit] tail_mem)
  rcases tolerance.2.2.2.2 with small | mixed
  · exact small_phase_actual_hull_approx_exclusive positive less_half slope_lower
      tolerance.2.2.2.1 small.2 lower upper digit child_data.1 child_data.2 lower_close upper_close level_close
  · have ordered := affine_actual_children_ordered tolerance.2.2.2.1.le mixed.2.le
      lower upper lower_close upper_close
    exact approx_affine_exclusive_of_actual_hulls lower upper ordered digit child_data.1 child_data.2
      lower_close upper_close level_close

end LambdaCantor.Last
