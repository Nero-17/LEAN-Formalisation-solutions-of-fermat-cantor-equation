import LambdaCantor.AE.UniformSeriesBounds
import LambdaCantor.First.AddressParameter

noncomputable section
namespace LambdaCantor.AE

def centeredDigitCoefficients (digits : ℕ → Bool) (index : ℕ) : ℝ :=
  if digits (index + 1) then 1 else 0

theorem centeredDigitCoefficients_bound (digits : ℕ → Bool) (index : ℕ) :
    |centeredDigitCoefficients digits index| ≤ 2 := by
  unfold centeredDigitCoefficients
  split_ifs <;> norm_num

theorem centered_address_series_identity (digits : ℕ → Bool) {ratio : ℝ}
    (hpositive : 0 < ratio) (hless : ratio < 1) :
    address ratio digits = (1 - ratio) *
      ((if digits 0 then (1 : ℝ) else 0) + normalizedDifference (centeredDigitCoefficients digits) ratio - 1) := by
  unfold address normalizedDifference centeredDigitCoefficients
  rw [← address_series_split hpositive.le hless digits]
  ring

theorem centered_address_hasDerivAt (digits : ℕ → Bool) {ratio : ℝ}
    (hpositive : 0 < ratio) (hless : ratio < 1) :
    HasDerivAt (fun parameter => address parameter digits)
      (-((if digits 0 then (1 : ℝ) else 0) +
          normalizedDifference (centeredDigitCoefficients digits) ratio - 1) +
        (1 - ratio) * deriv (normalizedDifference (centeredDigitCoefficients digits)) ratio) ratio := by
  have hseries := hasDerivAt_normalizedDifference (centeredDigitCoefficients digits)
    (centeredDigitCoefficients_bound digits) hpositive hless
  have hderivative := ((hasDerivAt_id ratio).const_sub 1).mul
    ((hseries.const_add (if digits 0 then (1 : ℝ) else 0)).sub_const 1)
  rw [← hseries.deriv] at hderivative
  have hmodel : HasDerivAt (fun parameter => (1 - parameter) *
      ((if digits 0 then (1 : ℝ) else 0) +
        normalizedDifference (centeredDigitCoefficients digits) parameter - 1))
      (-((if digits 0 then (1 : ℝ) else 0) +
          normalizedDifference (centeredDigitCoefficients digits) ratio - 1) +
        (1 - ratio) * deriv (normalizedDifference (centeredDigitCoefficients digits)) ratio) ratio := by
    have hfunction := hderivative.congr_of_eventuallyEq
      (f₁ := fun parameter => (1 - parameter) *
        ((if digits 0 then (1 : ℝ) else 0) +
          normalizedDifference (centeredDigitCoefficients digits) parameter - 1))
      (Filter.Eventually.of_forall (fun _ => rfl))
    simpa only [id_eq, neg_one_mul] using hfunction
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show ratio ∈ Set.Ioo (0 : ℝ) 1 from ⟨hpositive, hless⟩)]
    with parameter hparameter
  exact centered_address_series_identity digits hparameter.1 hparameter.2

theorem centered_address_second_hasDerivAt (digits : ℕ → Bool) {ratio : ℝ}
    (hpositive : 0 < ratio) (hless : ratio < 1) :
    HasDerivAt (deriv (fun parameter => address parameter digits))
      (-2 * deriv (normalizedDifference (centeredDigitCoefficients digits)) ratio +
        (1 - ratio) * deriv (deriv (normalizedDifference (centeredDigitCoefficients digits))) ratio) ratio := by
  have hseries := hasDerivAt_normalizedDifference (centeredDigitCoefficients digits)
    (centeredDigitCoefficients_bound digits) hpositive hless
  have hsecond := hasDerivAt_deriv_normalizedDifference (centeredDigitCoefficients digits)
    (centeredDigitCoefficients_bound digits) hpositive hless
  have hseries' := hseries.differentiableAt.hasDerivAt
  have hsecond' := hsecond.differentiableAt.hasDerivAt
  have hmodel := (((hseries'.const_add (if digits 0 then (1 : ℝ) else 0)).sub_const 1).neg).add
    (((hasDerivAt_id ratio).const_sub 1).mul hsecond')
  have hmodel' : HasDerivAt (fun parameter =>
      -((if digits 0 then (1 : ℝ) else 0) + normalizedDifference (centeredDigitCoefficients digits) parameter - 1) +
        (1 - parameter) * deriv (normalizedDifference (centeredDigitCoefficients digits)) parameter)
      (-2 * deriv (normalizedDifference (centeredDigitCoefficients digits)) ratio +
        (1 - ratio) * deriv (deriv (normalizedDifference (centeredDigitCoefficients digits))) ratio) ratio := by
    have hfunction := hmodel.congr_of_eventuallyEq
      (f₁ := fun parameter =>
        -((if digits 0 then (1 : ℝ) else 0) +
          normalizedDifference (centeredDigitCoefficients digits) parameter - 1) +
        (1 - parameter) * deriv (normalizedDifference (centeredDigitCoefficients digits)) parameter)
      (Filter.Eventually.of_forall (fun _ => rfl))
    apply hfunction.congr_deriv
    simp only [id_eq]
    ring
  apply hmodel'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show ratio ∈ Set.Ioo (0 : ℝ) 1 from ⟨hpositive, hless⟩)]
    with parameter hparameter
  exact (centered_address_hasDerivAt digits hparameter.1 hparameter.2).deriv

theorem centered_address_uniform_second_bound {upper : ℝ} (hpositive : 0 < upper) (hless : upper < 1) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ digits : ℕ → Bool,
      ∀ ratio ∈ Set.Ioc (0 : ℝ) upper,
        |deriv (deriv (fun parameter => address parameter digits)) ratio| ≤ constant := by
  obtain ⟨constant, hconstant, hbounds⟩ := normalizedDifference_uniform_C2_bounds hpositive hless
  refine ⟨3 * constant, by positivity, ?_⟩
  intro digits ratio hratio
  have hseries := hbounds (centeredDigitCoefficients digits) (centeredDigitCoefficients_bound digits) ratio hratio
  rw [(centered_address_second_hasDerivAt digits hratio.1 (hratio.2.trans_lt hless)).deriv]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_pos (show 0 < 1 - ratio by linarith [hratio.2]), abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hscaled := mul_le_mul_of_nonneg_left hseries.2.2 (show 0 ≤ 1 - ratio by linarith [hratio.2])
  nlinarith [hseries.2.1, mul_nonneg hratio.1.le hconstant.le]

end LambdaCantor.AE
