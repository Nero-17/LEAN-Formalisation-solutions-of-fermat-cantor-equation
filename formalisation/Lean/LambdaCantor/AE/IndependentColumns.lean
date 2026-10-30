import LambdaCantor.AE.PairProbability
import LambdaCantor.AE.AddressProbability
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
open MeasureTheory

namespace LambdaCantor.AE

theorem fourDigitMeasure_eq_pi :
    fourDigitMeasure = Measure.pi (fun _ : Fin 4 => fairDigitMeasure) := by
  apply Measure.ext_of_singleton
  intro digits
  rw [fourDigitMeasure,
    PMF.toMeasure_apply_singleton _ digits (measurableSet_singleton digits),
    PMF.uniformOfFintype_apply, Measure.pi_singleton]
  simp_rw [fairDigitMeasure,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply]
  have total_card : Fintype.card FourDigits = 16 := by decide
  rw [total_card]
  simp only [Fintype.card_bool, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← ENNReal.inv_pow]
  norm_num

/-- Transpose the actual array of four digits per position into four entire addresses. -/
def addressColumns : (ℕ → FourDigits) ≃ᵐ (Fin 4 → ℕ → Bool) :=
  (MeasurableEquiv.curry ℕ (Fin 4) Bool).symm |>.trans
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin 4 × ℕ => Bool)
      (Equiv.prodComm ℕ (Fin 4))).trans (MeasurableEquiv.curry (Fin 4) ℕ Bool))

theorem addressColumns_apply (sample : ℕ → FourDigits) (column : Fin 4) (index : ℕ) :
    addressColumns sample column index = sample index column := rfl

/-- The column law is proved by uncurry, index permutation, and curry of the product measure. -/
theorem map_addressColumns :
    fourAddressMeasure.map addressColumns = Measure.pi (fun _ : Fin 4 => addressProbability) := by
  have hrows : fourAddressMeasure = Measure.infinitePi
      (fun _ : ℕ => Measure.infinitePi (fun _ : Fin 4 => fairDigitMeasure)) := by
    simp only [fourAddressMeasure, Measure.infinitePi_eq_pi, fourDigitMeasure_eq_pi]
  rw [hrows]
  unfold addressColumns
  rw [MeasurableEquiv.coe_trans, ← Measure.map_map, MeasurableEquiv.coe_trans,
    ← Measure.map_map]
  · rw [Measure.infinitePi_map_curry_symm (fun (_ : ℕ) (_ : Fin 4) => fairDigitMeasure)]
    rw [Measure.infinitePi_map_piCongrLeft
      (X := fun _ : Fin 4 × ℕ => Bool)
      (fun _ : Fin 4 × ℕ => fairDigitMeasure) (Equiv.prodComm ℕ (Fin 4))]
    rw [Measure.infinitePi_map_curry (fun (_ : Fin 4) (_ : ℕ) => fairDigitMeasure),
      Measure.infinitePi_eq_pi]
    rfl
  all_goals fun_prop

/-- Exact finite-product integration for the four actual independent address columns. -/
theorem integral_product_addressColumns (functions : Fin 4 → (ℕ → Bool) → ℂ) :
    (∫ sample, ∏ column, functions column (fun index => sample index column)
      ∂fourAddressMeasure) =
    ∏ column, ∫ digits, functions column digits ∂addressProbability := by
  have hchange := integral_map_equiv (μ := fourAddressMeasure) addressColumns
    (fun columns => ∏ column, functions column (columns column))
  rw [map_addressColumns] at hchange
  change (∫ sample, ∏ column, functions column (addressColumns sample column)
    ∂fourAddressMeasure) = _
  rw [← hchange]
  exact integral_fintype_prod_eq_prod functions

end LambdaCantor.AE
