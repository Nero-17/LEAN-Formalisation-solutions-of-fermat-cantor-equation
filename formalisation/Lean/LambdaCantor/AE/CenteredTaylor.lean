import LambdaCantor.AE.CenteredCylinders
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
namespace LambdaCantor.AE

def centeredTaylorFirst (exponent displacement : ℝ) : ℝ :=
  exponent - exponent * (1 - displacement) ^ (exponent - 1)

def centeredTaylorSecond (exponent displacement : ℝ) : ℝ :=
  exponent * (exponent - 1) * (1 - displacement) ^ (exponent - 2)

theorem centeredTaylor_hasDerivAt (exponent displacement : ℝ) (hdisplacement : displacement < 1) :
    HasDerivAt (centeredTaylorRemainder exponent) (centeredTaylorFirst exponent displacement)
      displacement := by
  have haffine : HasDerivAt (fun value : ℝ => 1-value) (-1) displacement := by
    convert! (hasDerivAt_id displacement).const_sub (1 : ℝ) using 1 <;> simp
  have hpower := haffine.rpow_const (p := exponent)
    (Or.inl (show (1-displacement : ℝ) ≠ 0 by linarith))
  convert (hpower.sub_const 1).add ((hasDerivAt_id displacement).const_mul exponent) using 1 <;>
    first | rfl | (funext parameter; simp only [centeredTaylorRemainder, centeredTaylorFirst,
      Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq]; ring) |
      (simp only [centeredTaylorRemainder, centeredTaylorFirst, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq]; ring) | ring

theorem centeredTaylorFirst_hasDerivAt (exponent displacement : ℝ) (hdisplacement : displacement < 1) :
    HasDerivAt (centeredTaylorFirst exponent) (centeredTaylorSecond exponent displacement)
      displacement := by
  have haffine : HasDerivAt (fun value : ℝ => 1-value) (-1) displacement := by
    convert! (hasDerivAt_id displacement).const_sub (1 : ℝ) using 1 <;> simp
  have hpower := haffine.rpow_const (p := exponent - 1)
    (Or.inl (show (1-displacement : ℝ) ≠ 0 by linarith))
  convert (hasDerivAt_const displacement exponent).sub (hpower.const_mul exponent) using 1 <;>
    first | rfl | (funext parameter; simp only [centeredTaylorFirst, centeredTaylorSecond,
      Pi.sub_apply, Pi.mul_apply, id_eq, show exponent-1-1 = exponent-2 by ring]; ring) |
      (simp only [centeredTaylorFirst, centeredTaylorSecond, Pi.sub_apply, Pi.mul_apply, id_eq,
        show exponent-1-1 = exponent-2 by ring]; ring) | ring

/-- Uniform second-derivative control on a neighborhood of zero; valid for all
real exponents greater than one, including the range below two. -/
theorem centeredTaylorSecond_bound {exponent displacement : ℝ} (hexponent : 1 < exponent)
    (hdisplacement : displacement ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    |centeredTaylorSecond exponent displacement| ≤
      exponent * (exponent - 1) * max 1 ((1 / 2 : ℝ) ^ (exponent - 2)) := by
  have hexponentPositive : 0 < exponent := by linarith
  have hexponentMinus : 0 < exponent - 1 := by linarith
  have hbase : 0 < 1 - displacement := by linarith [hdisplacement.2]
  have hpower : (1 - displacement) ^ (exponent - 2) ≤
      max 1 ((1 / 2 : ℝ) ^ (exponent - 2)) := by
    by_cases hlarge : 0 ≤ exponent - 2
    · exact (Real.rpow_le_one hbase.le (by linarith [hdisplacement.1]) hlarge).trans (le_max_left _ _)
    · apply le_trans _ (le_max_right _ _)
      exact Real.rpow_le_rpow_of_nonpos (by norm_num)
        (by linarith [hdisplacement.2]) (le_of_not_ge hlarge)
  unfold centeredTaylorSecond
  rw [abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left hpower (by positivity)

theorem centeredTaylorFirst_bound {exponent displacement : ℝ} (hexponent : 1 < exponent)
    (hdisplacement : displacement ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    |centeredTaylorFirst exponent displacement| ≤
      (exponent * (exponent - 1) * max 1 ((1 / 2 : ℝ) ^ (exponent - 2))) * displacement := by
  have hestimate := (convex_Icc (0 : ℝ) (1 / 2)).norm_image_sub_le_of_norm_deriv_le
    (fun point hpoint => (centeredTaylorFirst_hasDerivAt exponent point (by linarith [hpoint.2])).differentiableAt)
    (fun point hpoint => by
      rw [(centeredTaylorFirst_hasDerivAt exponent point (by linarith [hpoint.2])).deriv]
      simpa only [Real.norm_eq_abs] using centeredTaylorSecond_bound hexponent hpoint)
    (show (0 : ℝ) ∈ Set.Icc 0 (1 / 2) by norm_num) hdisplacement
  simpa [centeredTaylorFirst, Real.norm_eq_abs, abs_of_nonneg hdisplacement.1] using hestimate

theorem centeredTaylorRemainder_quadratic_bound {exponent displacement : ℝ}
    (hexponent : 1 < exponent) (hdisplacement : displacement ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    |centeredTaylorRemainder exponent displacement| ≤
      (exponent * (exponent - 1) * max 1 ((1 / 2 : ℝ) ^ (exponent - 2))) * displacement ^ 2 := by
  have hexponentPositive : 0 < exponent := by linarith
  have hexponentMinus : 0 < exponent - 1 := by linarith
  have hconstant : 0 ≤ exponent * (exponent - 1) * max 1 ((1 / 2 : ℝ) ^ (exponent - 2)) := by
    positivity
  have hestimate := (convex_Icc (0 : ℝ) displacement).norm_image_sub_le_of_norm_deriv_le
    (fun point hpoint => (centeredTaylor_hasDerivAt exponent point
      (by linarith [hpoint.2, hdisplacement.2])).differentiableAt)
    (fun point hpoint => by
      rw [(centeredTaylor_hasDerivAt exponent point (by linarith [hpoint.2, hdisplacement.2])).deriv]
      rw [Real.norm_eq_abs]
      exact (centeredTaylorFirst_bound hexponent ⟨hpoint.1, hpoint.2.trans hdisplacement.2⟩).trans
        (mul_le_mul_of_nonneg_left hpoint.2 hconstant))
    (show (0 : ℝ) ∈ Set.Icc 0 displacement from ⟨le_rfl, hdisplacement.1⟩)
    (show displacement ∈ Set.Icc 0 displacement from ⟨hdisplacement.1, le_rfl⟩)
  simpa [centeredTaylorRemainder_zero, Real.norm_eq_abs, abs_of_nonneg hdisplacement.1,
    pow_two, mul_assoc] using hestimate

end LambdaCantor.AE
