import LambdaCantor.AE.CenteredSmallBallFrostman
import LambdaCantor.AE.CenteredPrefixSeparation

noncomputable section
open Set MeasureTheory Metric
namespace LambdaCantor.AE

/-- The first-coordinate separation estimate gives a root-law small-ball bound
for every closed interval, including intervals larger than the separation scale. -/
theorem rootLaw_interval_bound_of_first_coordinate_separation
    (root : (ℕ → Bool × Bool) → ℝ) (root_measurable : Measurable root)
    {contraction separation dimension left right : ℝ}
    (contraction_positive : 0 < contraction) (contraction_less_one : contraction < 1)
    (separation_positive : 0 < separation) (dimension_positive : 0 < dimension)
    (matching : contraction^dimension = (1/2 : ℝ))
    (separated : ∀ second : ℕ → Bool, ∀ depth : ℕ, ∀ first other : ℕ → Bool,
      (∃ position < depth, first position ≠ other position) →
      separation*contraction^depth ≤
        |root (fun index => (first index, second index)) - root (fun index => (other index, second index))|)
    (ordered : left ≤ right) :
    First.Roots.rootLaw root (Icc left right) ≤
      ENNReal.ofReal ((2*(right-left)/(separation*contraction))^dimension) := by
  have width_nonnegative : 0 ≤ right-left := sub_nonneg.mpr ordered
  have coefficient_nonnegative : 0 ≤ 2/(separation*contraction) := by positivity
  by_cases small : right-left ≤ separation/2
  · have bound := rootLaw_frostman_of_first_coordinate_separation root root_measurable
      contraction_positive contraction_less_one separation_positive dimension_positive matching separated
      measurableSet_Icc (by rw [Real.ediam_Icc]; exact ENNReal.ofReal_le_ofReal small)
    rw [Real.ediam_Icc,
      ENNReal.ofReal_rpow_of_nonneg width_nonnegative dimension_positive.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg coefficient_nonnegative _),
      ← Real.mul_rpow coefficient_nonnegative width_nonnegative] at bound
    convert bound using 1 <;> congr 2 <;> ring
  · letI := First.Roots.rootLaw_probability root root_measurable
    apply (prob_le_one : First.Roots.rootLaw root (Icc left right) ≤ 1).trans
    have base_one : 1 ≤ 2*(right-left)/(separation*contraction) := by
      apply (le_div_iff₀ (mul_pos separation_positive contraction_positive)).mpr
      have product := mul_lt_mul_of_pos_left contraction_less_one separation_positive
      nlinarith
    have power_one : 1 ≤ (2*(right-left)/(separation*contraction))^dimension :=
      Real.one_le_rpow base_one dimension_positive.le
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal power_one

end LambdaCantor.AE
