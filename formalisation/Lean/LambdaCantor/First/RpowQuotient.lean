import LambdaCantor.First.RpowTaylor
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace LambdaCantor

def rpowRemainderQuotient (exponent scale : ℝ) : ℝ :=
  ((1 - scale) ^ exponent - 1 + exponent * scale) / scale

/-- The divided quadratic remainder is O(scale), with bounded derivative,
uniformly on the positive half-interval. -/
theorem rpow_remainder_quotient_bounds (exponent : ℝ) :
    ∃ valueBound derivativeBound : ℝ, 0 < valueBound ∧ 0 < derivativeBound ∧
      ∀ scale ∈ Set.Ioc (0 : ℝ) (1 / 2),
        |rpowRemainderQuotient exponent scale| ≤ valueBound * scale ∧
        |deriv (rpowRemainderQuotient exponent) scale| ≤ derivativeBound := by
  obtain ⟨valueBound, hvalue_positive, hvalue⟩ := exists_rpow_quadratic_remainder_bound exponent
  obtain ⟨derivativeBound, hderivative_positive, hderivative⟩ :=
    exists_rpow_derivative_remainder_bound exponent
  refine ⟨valueBound, derivativeBound + valueBound, hvalue_positive,
    add_pos hderivative_positive hvalue_positive, ?_⟩
  intro scale hscale
  have hinterval : scale ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨hscale.1.le, hscale.2⟩
  have hbase : 1 - scale ≠ 0 := by linarith [hscale.2]
  have hpower := (((hasDerivAt_const scale (1 : ℝ)).sub (hasDerivAt_id scale)).rpow_const
    (p := exponent) (Or.inl hbase)).differentiableAt.hasDerivAt
  have hresidual : HasDerivAt
      (fun value : ℝ => (1 - value) ^ exponent - 1 + exponent * value)
      (deriv (fun value : ℝ => (1 - value) ^ exponent) scale + exponent) scale := by
    simpa only [Pi.sub_apply, id_eq, mul_one] using!
      (hpower.sub_const 1).add ((hasDerivAt_id scale).const_mul exponent)
  have hquotient : deriv (rpowRemainderQuotient exponent) scale =
      ((deriv (fun value : ℝ => (1 - value) ^ exponent) scale + exponent) * scale -
        ((1 - scale) ^ exponent - 1 + exponent * scale)) / scale ^ 2 := by
    simpa only [rpowRemainderQuotient, mul_one, id_eq] using!
      (hresidual.div (hasDerivAt_id scale) hscale.1.ne').deriv
  constructor
  · rw [rpowRemainderQuotient, abs_div, abs_of_pos hscale.1]
    apply (div_le_iff₀ hscale.1).mpr
    simpa only [pow_two, mul_assoc] using! hvalue scale hinterval
  · rw [hquotient, abs_div, abs_of_nonneg (sq_nonneg scale)]
    apply (div_le_iff₀ (sq_pos_of_pos hscale.1)).mpr
    calc
      _ ≤ |(deriv (fun value : ℝ => (1 - value) ^ exponent) scale + exponent) * scale| +
          |(1 - scale) ^ exponent - 1 + exponent * scale| := abs_sub _ _
      _ ≤ (derivativeBound * scale) * scale + valueBound * scale ^ 2 := by
        rw [abs_mul, abs_of_pos hscale.1]
        exact add_le_add
          (mul_le_mul_of_nonneg_right (hderivative scale hinterval) hscale.1.le)
          (hvalue scale hinterval)
      _ = _ := by ring

end LambdaCantor
