import LambdaCantor.First.Rational
import LambdaCantor.First.RationalComparison

noncomputable section
namespace LambdaCantor.First

/-- The comparison root satisfies the exact denominator coefficient, with
all differential and endpoint estimates discharged. -/
theorem rationalComparison_root_denominator_bound {exponent phase root : ℝ}
    (denominator : ℕ) (hexponent : 2 ≤ exponent) (hdenominator : 0 < denominator)
    (hphase : 0 ≤ phase)
    (hstep : phase - (exponent * Real.log (4 / 3) + Real.log exponent) / Real.log 4 ≤
      1 / (denominator : ℝ))
    (hroot : root ∈ Set.Icc (1 / 4 : ℝ) (1 / 2))
    (hzero : rationalComparison exponent phase root = 0) :
    root - 1 / 4 ≤ (3 / 2 : ℝ) ^ exponent * Real.log 4 /
      (2 * exponent * denominator) := by
  have hpositive : 0 < exponent := by linarith
  have hcontinuous : ContinuousOn (rationalComparison exponent phase)
      (Set.Icc (1 / 4 : ℝ) (1 / 2)) := by
    intro parameter hparameter
    exact (hasDerivAt_rationalComparison exponent phase parameter
      (by linarith [hparameter.1]) (by linarith [hparameter.2])).continuousAt.continuousWithinAt
  have hdifferentiable : DifferentiableOn ℝ (rationalComparison exponent phase)
      (Set.Ioo (1 / 4 : ℝ) (1 / 2)) := by
    intro parameter hparameter
    exact (hasDerivAt_rationalComparison exponent phase parameter
      (by linarith [hparameter.1]) (by linarith [hparameter.2])).differentiableAt.differentiableWithinAt
  have hbound := LambdaCantor.root_displacement_le (by norm_num) hroot hcontinuous
    hdifferentiable (show 0 < exponent * (2 : ℝ) ^ (1 - exponent) by positivity)
    (fun parameter hparameter => rationalComparison_derivative_le hexponent hphase
      ⟨hparameter.1.le, hparameter.2.le⟩) hzero
    (comparison_quarter_error (comparison_balance_phase hpositive) hstep)
  rwa [denominator_coefficient_identity hpositive (by exact_mod_cast hdenominator)] at hbound

/-- Every denominator admits a lattice phase and an interior comparison root
at the precise O(1/denominator) distance required in the theorem. -/
theorem exists_lattice_comparison_root (exponent : ℝ) (denominator : ℕ)
    (hexponent : 2 ≤ exponent) (hdenominator : 0 < denominator) :
    ∃ phase root : ℝ,
      (∃ numerator : ℤ, phase = numerator / (denominator : ℝ)) ∧
      root ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∧
      rationalComparison exponent phase root = 0 ∧
      root - 1 / 4 ≤ (3 / 2 : ℝ) ^ exponent * Real.log 4 /
        (2 * exponent * denominator) := by
  have hstep := next_lattice_point
    ((exponent * Real.log (4 / 3) + Real.log exponent) / Real.log 4)
    denominator hdenominator
  have hdenominatorReal : (1 : ℝ) ≤ denominator := by exact_mod_cast (Nat.succ_le_of_lt hdenominator)
  have hreciprocal : 1 / (denominator : ℝ) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (denominator : ℝ))).mpr hdenominatorReal
  have hphaseLower : (exponent * Real.log (4 / 3) + Real.log exponent) / Real.log 4 <
      ((⌊(denominator : ℝ) * ((exponent * Real.log (4 / 3) + Real.log exponent) / Real.log 4)⌋ + 1 : ℤ) : ℝ) /
        denominator := by simpa only [Int.cast_add, Int.cast_one] using (sub_pos.mp hstep.1)
  obtain ⟨root, hroot, _⟩ := exists_unique_rationalComparison_root hexponent hphaseLower
    (by simp only [Int.cast_add, Int.cast_one]; linarith [hstep.2])
  refine ⟨_, root, ⟨_, rfl⟩, hroot.1, hroot.2, ?_⟩
  exact rationalComparison_root_denominator_bound denominator hexponent hdenominator
    ((comparison_balance_phase_pos hexponent).trans hphaseLower).le (by simpa only [Int.cast_add, Int.cast_one] using hstep.2)
    ⟨hroot.1.1.le, hroot.1.2.le⟩ hroot.2

end LambdaCantor.First

