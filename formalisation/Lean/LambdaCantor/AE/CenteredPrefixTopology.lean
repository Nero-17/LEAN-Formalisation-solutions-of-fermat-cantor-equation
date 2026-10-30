import LambdaCantor.AE.CenteredPrefixLipschitz
import LambdaCantor.ParameterContinuity
import LambdaCantor.First.RootContinuity
import Mathlib.Tactic.Choose

noncomputable section
open Set
namespace LambdaCantor.AE

theorem continuous_centeredResidual_band {exponent lower upper : ℝ}
    (exponent_positive : 0 < exponent) (lower_positive : 0 < lower)
    (upper_less_one : upper < 1) (ordered : lower ≤ upper)
    (horizontalDepth verticalDepth tailDepth : ℕ) :
    Continuous (fun point : (ℕ → Bool × Bool) × Icc lower upper =>
      centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth point.1 point.2.val) := by
  have address_continuous := continuous_address_band lower_positive.le upper_less_one ordered
  have first_continuous : Continuous (fun point : (ℕ → Bool × Bool) × Icc lower upper =>
      address point.2.val (fun index => (point.1 index).1)) :=
    address_continuous.comp (continuous_snd.prodMk
      (continuous_pi (fun index => continuous_fst.comp ((continuous_apply index).comp continuous_fst))))
  have second_continuous : Continuous (fun point : (ℕ → Bool × Bool) × Icc lower upper =>
      address point.2.val (fun index => (point.1 index).2)) :=
    address_continuous.comp (continuous_snd.prodMk
      (continuous_pi (fun index => continuous_snd.comp ((continuous_apply index).comp continuous_fst))))
  have scalar_continuous : Continuous (fun point : (ℕ → Bool × Bool) × Icc lower upper =>
      (1-point.2.val^tailDepth+point.2.val^tailDepth*address point.2.val (fun index => (point.1 index).1))^exponent +
      ((1-point.2.val^verticalDepth+point.2.val^(verticalDepth+tailDepth)*address point.2.val (fun index => (point.1 index).2))^exponent-1) /
        point.2.val^(exponent*horizontalDepth)) := by
    have exponent_nonnegative := exponent_positive.le
    apply Continuous.add
    · apply Continuous.rpow_const
      · fun_prop
      · intro point
        exact Or.inr exponent_nonnegative
    · apply Continuous.div
      · apply Continuous.sub _ continuous_const
        apply Continuous.rpow_const
        · fun_prop
        · intro point
          exact Or.inr exponent_nonnegative
      · apply Continuous.rpow_const (by fun_prop)
        intro point
        exact Or.inr (mul_nonneg exponent_nonnegative (Nat.cast_nonneg horizontalDepth))
      · intro point
        exact ne_of_gt (Real.rpow_pos_of_pos (lower_positive.trans_le point.2.property.1) _)
  convert scalar_continuous using 1
  funext point
  exact centered_residual_scalar_formula exponent horizontalDepth verticalDepth tailDepth point.1
    (lower_positive.trans_le point.2.property.1) (point.2.property.2.trans_lt upper_less_one)

/-- Unique centered roots produce a continuous actual root map. No root-law
absolute continuity or dimension theorem is needed for this selection. -/
theorem exists_continuous_centered_root {exponent lower upper : ℝ}
    (exponent_positive : 0 < exponent) (lower_positive : 0 < lower)
    (upper_less_one : upper < 1) (ordered : lower ≤ upper)
    (horizontalDepth verticalDepth tailDepth : ℕ)
    (unique_roots : ∀ digits : ℕ → Bool × Bool, ∃! ratio : ℝ,
      ratio ∈ Icc lower upper ∧
        centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits ratio = 0) :
    ∃ root : (ℕ → Bool × Bool) → ℝ, Continuous root ∧
      (∀ digits, root digits ∈ Icc lower upper) ∧
      (∀ digits, centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits (root digits) = 0) := by
  classical
  choose root root_properties unique using unique_roots
  have continuous := continuous_unique_root
    (fun point : (ℕ → Bool × Bool) × Icc lower upper =>
      centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth point.1 point.2.val)
    (continuous_centeredResidual_band exponent_positive lower_positive upper_less_one ordered
      horizontalDepth verticalDepth tailDepth)
    (fun digits => (⟨root digits, (root_properties digits).1⟩ : Icc lower upper))
    (fun digits => (root_properties digits).2)
    (by
      intro digits ratio zero
      apply Subtype.ext
      exact unique digits ratio.val ⟨ratio.property, zero⟩)
  exact ⟨root, continuous_subtype_val.comp continuous,
    fun digits => (root_properties digits).1, fun digits => (root_properties digits).2⟩

end LambdaCantor.AE
