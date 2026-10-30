import LambdaCantor.AE.IndependentColumns
import LambdaCantor.AE.PairCharacteristic
import Mathlib.Tactic.FinCases

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace LambdaCantor.AE

theorem fourierChar_negative_conjugate (value : ℝ) :
    (Real.fourierChar (-value) : ℂ) = conj (Real.fourierChar value : ℂ) := by
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

theorem integral_addressFourier_positive (ratio frequency : ℝ) :
    (∫ digits, (Real.fourierChar (frequency * address ratio digits) : ℂ)
      ∂addressProbability) = conj (addressFourier ratio frequency) := by
  unfold addressFourier
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun digits => by
    change (Real.fourierChar (frequency * address ratio digits) : ℂ) =
      conj (Real.fourierChar (-(frequency * address ratio digits)) : ℂ)
    simpa only [neg_neg] using
      fourierChar_negative_conjugate (-(frequency * address ratio digits)))

theorem pair_character_pointwise (ratio frequency : ℝ) (sample : ℕ → FourDigits) :
    (Real.fourierChar (-(frequency * samplePairDifference ratio sample)) : ℂ) =
      (Real.fourierChar (-(frequency * address ratio (fun index => sample index 0))) : ℂ) *
      (Real.fourierChar (-(frequency * address ratio (fun index => sample index 1))) : ℂ) *
      (Real.fourierChar (frequency * address ratio (fun index => sample index 2)) : ℂ) *
      (Real.fourierChar (frequency * address ratio (fun index => sample index 3)) : ℂ) := by
  have hexponent : -(frequency * samplePairDifference ratio sample) =
      -(frequency * address ratio (fun index => sample index 0)) +
      -(frequency * address ratio (fun index => sample index 1)) +
      frequency * address ratio (fun index => sample index 2) +
      frequency * address ratio (fun index => sample index 3) := by
    unfold samplePairDifference addressPairDifference
    ring
  rw [hexponent]
  simp only [AddChar.map_add_eq_mul, Circle.coe_mul]

/-- Exact characteristic factorization for the actual four-address law, with independence
proved by the column reindexing theorem rather than assumed. -/
theorem pairCharacteristic_eq_fourth_power (ratio frequency : ℝ) :
    pairCharacteristic ratio frequency = (‖addressFourier ratio frequency‖ ^ 4 : ℝ) := by
  have hproduct := integral_product_addressColumns
    ![(fun digits => (Real.fourierChar (-(frequency * address ratio digits)) : ℂ)),
      (fun digits => (Real.fourierChar (-(frequency * address ratio digits)) : ℂ)),
      (fun digits => (Real.fourierChar (frequency * address ratio digits) : ℂ)),
      (fun digits => (Real.fourierChar (frequency * address ratio digits) : ℂ))]
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero] at hproduct
  have hfactor : pairCharacteristic ratio frequency =
      addressFourier ratio frequency * addressFourier ratio frequency *
        conj (addressFourier ratio frequency) * conj (addressFourier ratio frequency) := by
    calc
      pairCharacteristic ratio frequency =
          ∫ sample : ℕ → FourDigits,
            (Real.fourierChar (-(frequency * address ratio (fun index => sample index 0))) : ℂ) *
            (Real.fourierChar (-(frequency * address ratio (fun index => sample index 1))) : ℂ) *
            (Real.fourierChar (frequency * address ratio (fun index => sample index 2)) : ℂ) *
            (Real.fourierChar (frequency * address ratio (fun index => sample index 3)) : ℂ)
            ∂fourAddressMeasure :=
        integral_congr_ae (Filter.Eventually.of_forall (pair_character_pointwise ratio frequency))
      _ = addressFourier ratio frequency * addressFourier ratio frequency *
          (∫ digits : ℕ → Bool,
            (Real.fourierChar (frequency * address ratio digits) : ℂ) ∂addressProbability) *
          (∫ digits : ℕ → Bool,
            (Real.fourierChar (frequency * address ratio digits) : ℂ) ∂addressProbability) := hproduct
      _ = _ := congrArg (fun value : ℂ =>
          addressFourier ratio frequency * addressFourier ratio frequency * value * value)
        (integral_addressFourier_positive ratio frequency)
  rw [hfactor]
  have hnorm : addressFourier ratio frequency * conj (addressFourier ratio frequency) =
      (‖addressFourier ratio frequency‖ ^ 2 : ℝ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  calc
    _ = (addressFourier ratio frequency * conj (addressFourier ratio frequency)) ^ 2 := by ring
    _ = _ := by rw [hnorm]; push_cast; ring

theorem addressFourier_neg (ratio frequency : ℝ) :
    addressFourier ratio (-frequency) = conj (addressFourier ratio frequency) := by
  unfold addressFourier
  simp only [neg_mul, neg_neg]
  exact integral_addressFourier_positive ratio frequency

theorem expected_fourier_annularCutoff_eq_fourth_power (ratio frequency : ℝ) :
    (∫ sample, FourierTransform.fourier complexAnnularCutoff
      (frequency * samplePairDifference ratio sample) ∂fourAddressMeasure) =
    ∫ integrationVariable : ℝ, (annularCutoff integrationVariable : ℂ) *
      (‖addressFourier ratio (integrationVariable * frequency)‖ ^ 4 : ℝ) := by
  rw [expected_fourier_annularCutoff]
  simp only [pairCharacteristic_eq_fourth_power, complexAnnularCutoff]

end LambdaCantor.AE
