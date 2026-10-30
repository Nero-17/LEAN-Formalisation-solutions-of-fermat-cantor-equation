import LambdaCantor.Last.TwoBandNonlinear
import LambdaCantor.Last.OuterQuotient
import Mathlib.Tactic.FunProp

noncomputable section
namespace LambdaCantor.Last

/-- Direct four-child covering for the affine sum. This avoids every
thickness presentation and Gap Lemma dependency in the irrational route. -/
theorem two_band_affine_sum_cover {ratio slope level : ℝ}
    (hthird : (1 / 3 : ℝ) < ratio) (hhalf : ratio < 1 / 2)
    (hslower : 1 - ratio ≤ slope) (hsupper : slope ≤ 1)
    (hlevel : level ∈ Set.Icc (0 : ℝ) (1 + slope)) :
    ∃ first ∈ cantorSet ratio, ∃ second ∈ cantorSet ratio, slope * first + second = level := by
  have hpositive : 0 < ratio := by linarith
  have hless : ratio < 1 := by linarith
  let function : (ℝ × ℝ) → ℝ := fun point => slope * point.1 + point.2
  have growth : CoordinateGrowth function slope slope 1 1 := by
    constructor
    · intro first second height hfirst hsecond hheight horder
      constructor <;> dsimp [function] <;> ring_nf <;> rfl
    · intro first second width hfirst hsecond hwidth horder
      constructor <;> dsimp [function] <;> ring_nf <;> rfl
  have houter : (1 - 2 * ratio) * slope < ratio := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsupper) (show 0 ≤ 1 - 2 * ratio by linarith)]
  have hmiddle : 1 - 2 * ratio < slope := by linarith
  obtain ⟨point, hpoint, hpoint_level⟩ := nonlinear_closed_hull_filled growth
    (by dsimp [function]; fun_prop) hpositive hhalf (by simpa using houter) (by simpa using hmiddle)
    (show level ∈ Set.Icc (function (0, 0)) (function (1, 1)) by simpa [function, add_comm] using hlevel)
  exact ⟨point.1, hpoint.1, point.2, hpoint.2, hpoint_level⟩

theorem two_band_outer_quotient_lower_half {ratio quotient : ℝ}
    (hthird : (1 / 3 : ℝ) < ratio) (hhalf : ratio < 1 / 2)
    (hqlower : 1 - ratio ≤ quotient) (hqupper : quotient ≤ 1) :
    quotient ∈ outerQuotients ratio := by
  have hpositive : 0 < ratio := by linarith
  have hless : ratio < 1 := by linarith
  let level := quotient + (quotient - 1) * (1 - ratio) / ratio
  have hlevel_identity : level = (quotient - 1 + ratio) / ratio := by
    dsimp [level]
    field_simp [hpositive.ne']
    <;> ring
  have hlevel : level ∈ Set.Icc (0 : ℝ) (1 + quotient) := by
    constructor
    · rw [hlevel_identity]
      exact div_nonneg (by linarith) hpositive.le
    · have hnonpositive : (quotient - 1) * (1 - ratio) / ratio ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)) hpositive.le
      dsimp [level]
      linarith
  obtain ⟨first, hfirst, second, hsecond, hsum⟩ := two_band_affine_sum_cover hthird hhalf hqlower hqupper hlevel
  have hfirst_bounds := cantorSet_subset_unitInterval hpositive.le hless hfirst
  have hdenominator : 0 < 1 - ratio + ratio * (1 - first) := by
    nlinarith [mul_nonneg hpositive.le (sub_nonneg.mpr hfirst_bounds.2)]
  refine ⟨1 - ratio + ratio * second, ⟨second, hsecond, rfl⟩,
    1 - ratio + ratio * (1 - first), ⟨1 - first, one_sub_mem_cantorSet hpositive.le hless hfirst, rfl⟩, ?_⟩
  have hscaled := congrArg (fun value : ℝ => ratio * value) hsum
  have hlevel_scaled : ratio * level = quotient - 1 + ratio := by
    rw [hlevel_identity]
    field_simp [hpositive.ne']
  rw [hlevel_scaled] at hscaled
  apply (eq_div_iff hdenominator.ne').mpr
  nlinarith

theorem two_band_outerQuotients_eq_interval {ratio : ℝ}
    (hthird : (1 / 3 : ℝ) < ratio) (hhalf : ratio < 1 / 2) :
    outerQuotients ratio = Set.Icc (1 - ratio) (1 - ratio)⁻¹ := by
  have hpositive : 0 < ratio := by linarith
  have hless : ratio < 1 := by linarith
  have hcomplement : 0 < 1 - ratio := by linarith
  apply Set.Subset.antisymm (outerQuotients_subset hpositive.le hless)
  intro quotient hquotient
  by_cases hqupper : quotient ≤ 1
  · exact two_band_outer_quotient_lower_half hthird hhalf hquotient.1 hqupper
  · have hqpositive : 0 < quotient := by linarith
    have hlower_inverse : 1 - ratio ≤ quotient⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hqpositive]
      have hbound := (le_div_iff₀ hcomplement).mp (show quotient ≤ 1 / (1 - ratio) by
        simpa only [inv_eq_one_div] using hquotient.2)
      nlinarith
    have hupper_inverse : quotient⁻¹ ≤ 1 := by
      have hbound := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) (show 1 ≤ quotient by linarith)
      simpa only [inv_eq_one_div, div_one] using hbound
    obtain ⟨first, hfirst, second, hsecond, hquotient_eq⟩ :=
      two_band_outer_quotient_lower_half hthird hhalf hlower_inverse hupper_inverse
    refine ⟨second, hsecond, first, hfirst, ?_⟩
    simpa only [inv_inv, inv_div] using congrArg (fun value : ℝ => value⁻¹) hquotient_eq

end LambdaCantor.Last
