import LambdaCantor.AE.SobolevTransport
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Jensen

noncomputable section
open MeasureTheory Finset
open scoped BigOperators

namespace LambdaCantor.AE

theorem weighted_sobolev_amplitude_bound {Index : Type*} (indices : Finset Index)
    (weight amplitude : Index → ℝ) {regularity : ℝ}
    (hweight : ∀ index ∈ indices, 0 ≤ weight index)
    (hmass : ∑ index ∈ indices, weight index = 1)
    (hamplitude : ∀ index ∈ indices, 0 ≤ amplitude index)
    (hregularity : 0 ≤ regularity) :
    (∑ index ∈ indices, weight index * amplitude index ^ (1 / (1 + regularity))) ≤
      (∑ index ∈ indices, weight index * amplitude index ^ 2) ^
        (1 / (2 * (1 + regularity))) := by
  have hexponentNonnegative : 0 ≤ 1 / (2 * (1 + regularity)) := by positivity
  have hexponentOne : 1 / (2 * (1 + regularity)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + regularity))).mpr
    linarith
  have hjensen := (Real.concaveOn_rpow hexponentNonnegative hexponentOne).le_map_sum
    hweight hmass (fun index (_ : index ∈ indices) => sq_nonneg (amplitude index))
  simp only [smul_eq_mul] at hjensen
  have sum_identity :
      (∑ index ∈ indices, weight index * amplitude index ^ (1 / (1 + regularity))) =
        ∑ index ∈ indices, weight index * (amplitude index ^ 2) ^
          (1 / (2 * (1 + regularity))) := by
    apply Finset.sum_congr rfl
    intro index hindex
    congr 1
    rw [← Real.rpow_natCast_mul (hamplitude index hindex)]
    congr 1
    field_simp
    all_goals norm_num
  exact sum_identity.trans_le hjensen

theorem finite_mixture_L1_distance_le {Index : Type*} (indices : Finset Index)
    (weight : Index → ℝ) (first second : Index → ℝ → ℝ)
    (hweight : ∀ index ∈ indices, 0 ≤ weight index)
    (hfirst : ∀ index ∈ indices, Integrable (first index))
    (hsecond : ∀ index ∈ indices, Integrable (second index)) :
    (∫ value : ℝ, |(∑ index ∈ indices, weight index * first index value) -
      ∑ index ∈ indices, weight index * second index value|) ≤
      ∑ index ∈ indices, weight index * ∫ value : ℝ, |first index value - second index value| := by
  have hfirstSum : Integrable (fun value => ∑ index ∈ indices, weight index * first index value) :=
    integrable_finset_sum _ (fun index hindex => (hfirst index hindex).const_mul _)
  have hsecondSum : Integrable (fun value => ∑ index ∈ indices, weight index * second index value) :=
    integrable_finset_sum _ (fun index hindex => (hsecond index hindex).const_mul _)
  have hsum : Integrable (fun value =>
      ∑ index ∈ indices, weight index * |first index value - second index value|) :=
    integrable_finset_sum _ (fun index hindex =>
      ((hfirst index hindex).sub (hsecond index hindex)).abs.const_mul _)
  calc
    _ ≤ ∫ value : ℝ, ∑ index ∈ indices,
        weight index * |first index value - second index value| := by
      apply integral_mono (hfirstSum.sub hsecondSum).abs hsum
      intro value
      change |(∑ index ∈ indices, weight index * first index value) -
        ∑ index ∈ indices, weight index * second index value| ≤
          ∑ index ∈ indices, weight index * |first index value - second index value|
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ index ∈ indices,
            |weight index * first index value - weight index * second index value| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro index hindex
          rw [← mul_sub, abs_mul, abs_of_nonneg (hweight index hindex)]
    _ = _ := by
      have integral_sum :
          (∫ value : ℝ, ∑ index ∈ indices,
            weight index * |first index value - second index value|) =
          ∑ index ∈ indices, ∫ value : ℝ,
            weight index * |first index value - second index value| := by
        simpa only [Pi.sub_apply] using
          (integral_finset_sum indices (fun index hindex =>
            ((hfirst index hindex).sub (hsecond index hindex)).abs.const_mul (weight index)))
      rw [integral_sum]
      simp_rw [integral_const_mul]

/-- Finite address mixtures use the averaged squared Sobolev amplitude,
with the exponent required by the freezing-series estimate. -/
theorem finite_mixture_transport_bound {Index : Type*} (indices : Finset Index)
    (weight amplitude : Index → ℝ) (first second : Index → ℝ → ℝ)
    {constant cost regularity : ℝ}
    (hweight : ∀ index ∈ indices, 0 ≤ weight index)
    (hmass : ∑ index ∈ indices, weight index = 1)
    (hamplitude : ∀ index ∈ indices, 0 ≤ amplitude index)
    (hfirst : ∀ index ∈ indices, Integrable (first index))
    (hsecond : ∀ index ∈ indices, Integrable (second index))
    (hconstant : 0 ≤ constant) (hcost : 0 ≤ cost) (hregularity : 0 ≤ regularity)
    (hcomponent : ∀ index ∈ indices,
      (∫ value : ℝ, |first index value - second index value|) ≤
        constant * amplitude index ^ (1 / (1 + regularity)) *
          cost ^ (regularity / (1 + regularity))) :
    (∫ value : ℝ, |(∑ index ∈ indices, weight index * first index value) -
      ∑ index ∈ indices, weight index * second index value|) ≤
      constant * (∑ index ∈ indices, weight index * amplitude index ^ 2) ^
        (1 / (2 * (1 + regularity))) * cost ^ (regularity / (1 + regularity)) := by
  apply (finite_mixture_L1_distance_le indices weight first second hweight hfirst hsecond).trans
  calc
    _ ≤ ∑ index ∈ indices, weight index *
        (constant * amplitude index ^ (1 / (1 + regularity)) *
          cost ^ (regularity / (1 + regularity))) :=
      Finset.sum_le_sum (fun index hindex =>
        mul_le_mul_of_nonneg_left (hcomponent index hindex) (hweight index hindex))
    _ = constant * (∑ index ∈ indices, weight index * amplitude index ^ (1 / (1 + regularity))) *
        cost ^ (regularity / (1 + regularity)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro index hindex
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (weighted_sobolev_amplitude_bound indices weight amplitude hweight hmass hamplitude hregularity)
        hconstant) (Real.rpow_nonneg hcost _)

end LambdaCantor.AE
