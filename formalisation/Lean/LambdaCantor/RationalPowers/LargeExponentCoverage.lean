import LambdaCantor.RationalPowers.LargeExponentFiniteLayers
import LambdaCantor.RationalPowers.LargeExponentTail
import Mathlib.Algebra.Order.Archimedean.Basic

noncomputable section
namespace LambdaCantor.RationalPowers
open Integer

theorem largeExponent_normalized_layer {exponent : ℝ} (large : (3 : ℝ)^7 ≤ exponent) :
    ∃ layer : ℕ, 7 ≤ layer ∧ exponent/(3 : ℝ)^layer ∈ Set.Icc (1 : ℝ) 3 := by
  obtain ⟨layer,lower,upper⟩ := exists_nat_pow_near
    (show (1 : ℝ) ≤ exponent by norm_num at large ⊢; linarith)
    (by norm_num : (1 : ℝ) < 3)
  have layer_large : 7 ≤ layer := by
    by_contra contrary
    have comparison : (3 : ℝ)^(layer+1) ≤ (3 : ℝ)^7 :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact (not_lt_of_ge large) (upper.trans_le comparison)
  refine ⟨layer,layer_large,?_,?_⟩
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ)^layer)).2
    simpa only [one_mul] using lower
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ)^layer)).2
    rw [pow_succ] at upper
    nlinarith

end LambdaCantor.RationalPowers
