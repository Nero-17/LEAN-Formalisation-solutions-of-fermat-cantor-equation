import LambdaCantor.RealPowers.DirectEndpointSource
import LambdaCantor.RealPowers.ReciprocalEndpointSource
import Mathlib.Algebra.Order.Archimedean.Basic

noncomputable section
namespace LambdaCantor.RealPowers
open Integer Last

theorem finite_normalized_slope_irrational {exponent : ℝ}
    (irrational : Irrational exponent) (first second : ℕ → Bool) (depth shift : ℕ) :
    Irrational (exponent*(1/3 : ℝ)^shift*
      finiteOuterEndpoint first depth/finiteOuterEndpoint second depth) := by
  have result := finite_endpoint_slope_irrational irrational first second depth (-(shift : ℤ))
  have ternary_shift : (3 : ℝ)^(-(shift : ℤ)) = (1/3 : ℝ)^shift := by
    simp [zpow_neg, one_div_pow]
  rw [ternary_shift] at result
  convert result using 1 <;> ring

/-- Actual positive Hausdorff dimension at the middle-third parameter for
every irrational real exponent greater than one. The proof constructs both
source orientations, then actual integer-depth Cantor cylinders. -/
theorem irrational_real_power_positive_dimension {exponent : ℝ}
    (irrational : Irrational exponent) (exponent_gt_one : 1 < exponent) :
    0 < dimH (intersection exponent (1/3)) := by
  have exponent_positive : 0 < exponent := by linarith
  obtain ⟨shift, power_lower, power_upper⟩ :=
    exists_nat_pow_near exponent_gt_one.le (by norm_num : (1 : ℝ) < 3)
  have power_positive : 0 < (3 : ℝ)^shift := by positivity
  have normalized_lower : 1 ≤ exponent/(3 : ℝ)^shift :=
    (le_div_iff₀ power_positive).mpr (by simpa using power_lower)
  have normalized_upper : exponent/(3 : ℝ)^shift ≤ 3 := by
    apply (div_le_iff₀ power_positive).mpr
    rw [pow_succ] at power_upper
    nlinarith
  obtain ⟨first, second, depth, direct | reciprocal⟩ :=
    finite_endpoint_normalized_slope (exponent/(3 : ℝ)^shift) normalized_lower normalized_upper
  · have scale_identity : exponent*(1/3 : ℝ)^shift = exponent/(3 : ℝ)^shift := by
      rw [one_div_pow]
      ring
    have source_identity : exponent*(1/3 : ℝ)^shift*
        scalarWordMap (1/3) (true::scalarPrefix first depth) 0/
          scalarWordMap (1/3) (true::scalarPrefix second depth) 0 =
        (exponent/(3 : ℝ)^shift)*(finiteOuterEndpoint first depth/finiteOuterEndpoint second depth) := by
      rw [finiteOuterEndpoint_word, finiteOuterEndpoint_word, scale_identity]
      ring
    have good : GoodSlope (exponent*(1/3 : ℝ)^shift*
        scalarWordMap (1/3) (true::scalarPrefix first depth) 0/
          scalarWordMap (1/3) (true::scalarPrefix second depth) 0) := by
      rw [source_identity]
      apply Or.inl
      constructor <;> linarith [direct.1, direct.2]
    apply irrational_positive_from_direct_endpoint_pair exponent_gt_one irrational
      (true::scalarPrefix second depth) (true::scalarPrefix first depth)
      (by simp) (by simpa only [finiteOuterEndpoint_word] using (finiteOuterEndpoint_bounds second depth).1)
      (by simpa only [finiteOuterEndpoint_word] using (finiteOuterEndpoint_bounds first depth).1) shift good
    intro rational
    simpa only [finiteOuterEndpoint_word] using
      (finite_normalized_slope_irrational irrational first second depth shift).ne_rat rational
  · have scale_identity : exponent*(1/3 : ℝ)^(shift+1) = (exponent/(3 : ℝ)^shift)/3 := by
      rw [pow_succ, one_div_pow]
      ring
    have source_identity : exponent*(1/3 : ℝ)^(shift+1)*
        scalarWordMap (1/3) (true::scalarPrefix first depth) 0/
          scalarWordMap (1/3) (true::scalarPrefix second depth) 0 =
        ((exponent/(3 : ℝ)^shift)/3)*(finiteOuterEndpoint first depth/finiteOuterEndpoint second depth) := by
      rw [finiteOuterEndpoint_word, finiteOuterEndpoint_word, scale_identity]
      ring
    have source_positive : 0 < exponent*(1/3 : ℝ)^(shift+1)*
        scalarWordMap (1/3) (true::scalarPrefix first depth) 0/
          scalarWordMap (1/3) (true::scalarPrefix second depth) 0 := by
      rw [source_identity]
      exact mul_pos (div_pos (div_pos exponent_positive power_positive) (by norm_num))
        (div_pos (finiteOuterEndpoint_bounds first depth).1 (finiteOuterEndpoint_bounds second depth).1)
    have good : GoodSlope (1/(exponent*(1/3 : ℝ)^(shift+1)*
        scalarWordMap (1/3) (true::scalarPrefix first depth) 0/
          scalarWordMap (1/3) (true::scalarPrefix second depth) 0)) := by
      have direct_lower : (11/9 : ℝ) < 1/(exponent*(1/3 : ℝ)^(shift+1)*
          scalarWordMap (1/3) (true::scalarPrefix first depth) 0/
            scalarWordMap (1/3) (true::scalarPrefix second depth) 0) := by
        apply (lt_div_iff₀ source_positive).mpr
        rw [source_identity]
        nlinarith [reciprocal.2]
      have direct_upper : 1/(exponent*(1/3 : ℝ)^(shift+1)*
          scalarWordMap (1/3) (true::scalarPrefix first depth) 0/
            scalarWordMap (1/3) (true::scalarPrefix second depth) 0) < (2027/1624 : ℝ) := by
        apply (div_lt_iff₀ source_positive).mpr
        rw [source_identity]
        nlinarith [reciprocal.1]
      apply Or.inl
      constructor <;> linarith [direct_lower, direct_upper]
    apply irrational_positive_from_reciprocal_endpoint_pair exponent_gt_one irrational
      (true::scalarPrefix second depth) (true::scalarPrefix first depth)
      (by simp) (by simpa only [finiteOuterEndpoint_word] using (finiteOuterEndpoint_bounds second depth).1)
      (by simpa only [finiteOuterEndpoint_word] using (finiteOuterEndpoint_bounds first depth).1) (shift+1) good
    intro rational
    rw [finiteOuterEndpoint_word, finiteOuterEndpoint_word]
    simpa only [one_div] using
      (finite_normalized_slope_irrational irrational first second depth (shift+1)).inv.ne_rat rational

end LambdaCantor.RealPowers

