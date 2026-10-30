import LambdaCantor.First.NormalizedRealResidual
import LambdaCantor.First.TailDecay
import LambdaCantor.First.CylinderCalculus

noncomputable section
namespace LambdaCantor

def realRootTail (padding : ℕ) (digits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  1 - ratio ^ padding * address ratio digits

def realNormalizationError (exponent phase : ℝ) (depth padding : ℕ)
    (digits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  ratio ^ phase * realRootTail padding digits ratio *
    rpowRemainderQuotient exponent (ratio ^ depth * realRootTail padding digits ratio)

theorem realRootTail_bounds {ratio : ℝ} (hpositive : 0 < ratio) (hlt : ratio < 1)
    {padding : ℕ} (hpadding : 1 ≤ padding) (digits : ℕ → Bool) :
    0 < realRootTail padding digits ratio ∧ realRootTail padding digits ratio ≤ 1 := by
  have hnonnegative := address_nonnegative hpositive.le hlt digits
  have hbounded := address_le_one hpositive.le hlt digits
  have hpower : ratio ^ padding < 1 := pow_lt_one₀ hpositive.le hlt (by omega)
  have hproduct : ratio ^ padding * address ratio digits ≤ ratio ^ padding := by
    simpa using mul_le_mul_of_nonneg_left hbounded (pow_nonneg hpositive.le padding)
  dsimp [realRootTail]
  constructor <;> nlinarith [mul_nonneg (pow_nonneg hpositive.le padding) hnonnegative]

theorem hasDerivAt_realRootTail {ratio : ℝ} (hpositive : 0 < ratio) (hlt : ratio < 1)
    (padding : ℕ) (digits : ℕ → Bool) :
    HasDerivAt (realRootTail padding digits)
      (-deriv (fun parameter => parameter ^ padding * address parameter digits) ratio) ratio := by
  simpa only [realRootTail, zero_sub] using!
    (hasDerivAt_const ratio (1 : ℝ)).sub
      (hasDerivAt_scaled_address hpositive hlt padding digits).differentiableAt.hasDerivAt

theorem differentiableAt_rpowRemainderQuotient (exponent : ℝ) {scale : ℝ}
    (hscale : scale ∈ Set.Ioc (0 : ℝ) (1 / 2)) :
    DifferentiableAt ℝ (rpowRemainderQuotient exponent) scale := by
  have hpower := (((hasDerivAt_const scale (1 : ℝ)).sub (hasDerivAt_id scale)).rpow_const
    (p := exponent) (Or.inl (by linarith [hscale.2] : 1 - scale ≠ 0)))
  exact (((hpower.sub_const 1).add ((hasDerivAt_id scale).const_mul exponent)).div
    (hasDerivAt_id scale) hscale.1.ne').differentiableAt

/-- Uniform finite C1 bounds for the genuine tail error. -/
theorem realNormalizationError_bounds (exponent : ℝ) :
    ∃ valueBound derivativeBound : ℝ, 0 < valueBound ∧ 0 < derivativeBound ∧
      ∀ (lower upper ratio phase phaseBound : ℝ) (depth padding : ℕ) (digits : ℕ → Bool),
        0 < lower → lower ≤ ratio → ratio ≤ upper → upper < 1 →
        0 ≤ phase → phase ≤ phaseBound → 1 ≤ padding → upper ^ depth ≤ 1 / 2 →
        (padding : ℝ) * upper ^ (padding - 1) +
          upper ^ padding * addressParameterDerivativeBound upper ≤ 1 →
        |realNormalizationError exponent phase depth padding digits ratio| ≤ valueBound * upper ^ depth ∧
        |deriv (realNormalizationError exponent phase depth padding digits) ratio| ≤
          (phaseBound / lower + 1) * valueBound * upper ^ depth +
            derivativeBound * ((depth : ℝ) * upper ^ (depth - 1) + upper ^ depth) := by
  obtain ⟨valueBound, derivativeBound, hvalue, hderivative, hquotient⟩ :=
    rpow_remainder_quotient_bounds exponent
  refine ⟨valueBound, derivativeBound, hvalue, hderivative, ?_⟩
  intro lower upper ratio phase phaseBound depth padding digits hlower hlow hhigh hupper
    hphase hphaseBound hpadding hsmall hpaddingDerivative
  have hphaseBoundNonnegative : 0 ≤ phaseBound := hphase.trans hphaseBound
  have hratio := lt_of_lt_of_le hlower hlow
  have hlt := lt_of_le_of_lt hhigh hupper
  have htail := realRootTail_bounds hratio hlt hpadding digits
  have htailPositive := htail.1
  have htailDerivative : |deriv (realRootTail padding digits) ratio| ≤ 1 := by
    rw [(hasDerivAt_realRootTail hratio hlt padding digits).deriv, abs_neg]
    exact (scaled_address_derivative_bound hratio hhigh hupper padding digits).trans hpaddingDerivative
  have hpower := pow_le_pow_left₀ hratio.le hhigh depth
  have hscaleBound : ratio ^ depth * realRootTail padding digits ratio ≤ upper ^ depth :=
    (mul_le_of_le_one_right (pow_nonneg hratio.le _) htail.2).trans hpower
  have hscale : ratio ^ depth * realRootTail padding digits ratio ∈ Set.Ioc (0 : ℝ) (1 / 2) :=
    ⟨mul_pos (pow_pos hratio _) htail.1, hscaleBound.trans hsmall⟩
  have hphasePower : 0 < ratio ^ phase := Real.rpow_pos_of_pos hratio phase
  have hphaseOne : ratio ^ phase ≤ 1 := Real.rpow_le_one hratio.le hlt.le hphase
  have hphaseDerivative : |phase * ratio ^ (phase - 1)| ≤ phaseBound / lower := by
    rw [Real.rpow_sub_one hratio.ne', abs_of_nonneg (by positivity)]
    calc
      phase * (ratio ^ phase / ratio) ≤ phaseBound * (1 / lower) := by
        apply mul_le_mul hphaseBound
        · exact div_le_div₀ (by norm_num) hphaseOne hlower hlow
        · positivity
        · exact hphase.trans hphaseBound
      _ = _ := by ring
  have htailD := (hasDerivAt_realRootTail hratio hlt padding digits).differentiableAt.hasDerivAt
  have hscaleD := ((hasDerivAt_id ratio).pow depth).mul htailD
  have hscaleDerivative : |(depth : ℝ) * ratio ^ (depth - 1) *
      realRootTail padding digits ratio + ratio ^ depth * deriv (realRootTail padding digits) ratio| ≤
      (depth : ℝ) * upper ^ (depth - 1) + upper ^ depth := by
    calc
      _ ≤ |(depth : ℝ) * ratio ^ (depth - 1) * realRootTail padding digits ratio| +
          |ratio ^ depth * deriv (realRootTail padding digits) ratio| := abs_add_le _ _
      _ = (depth : ℝ) * ratio ^ (depth - 1) * realRootTail padding digits ratio +
          ratio ^ depth * |deriv (realRootTail padding digits) ratio| := by
        rw [abs_of_nonneg (by positivity), abs_mul, abs_of_pos (pow_pos hratio _)]
      _ ≤ (depth : ℝ) * ratio ^ (depth - 1) * 1 + ratio ^ depth * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left htail.2 (by positivity))
          (mul_le_mul_of_nonneg_left htailDerivative (pow_nonneg hratio.le _))
      _ ≤ _ := by
        simp only [mul_one]
        exact add_le_add (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hratio.le hhigh _) (Nat.cast_nonneg depth)) hpower
  have hproduct : 0 ≤ ratio ^ phase * realRootTail padding digits ratio := by positivity
  have hproductOne : ratio ^ phase * realRootTail padding digits ratio ≤ 1 :=
    (mul_le_of_le_one_right hphasePower.le htail.2).trans hphaseOne
  have hproductD : |phase * ratio ^ (phase - 1) * realRootTail padding digits ratio +
      ratio ^ phase * deriv (realRootTail padding digits) ratio| ≤ phaseBound / lower + 1 := by
    calc
      _ ≤ |phase * ratio ^ (phase - 1)| * |realRootTail padding digits ratio| +
          |ratio ^ phase| * |deriv (realRootTail padding digits) ratio| := by
        simpa only [abs_mul] using abs_add_le
          (phase * ratio ^ (phase - 1) * realRootTail padding digits ratio)
          (ratio ^ phase * deriv (realRootTail padding digits) ratio)
      _ ≤ _ := by
        rw [abs_of_pos htail.1, abs_of_pos hphasePower]
        simpa only [mul_one, one_mul] using add_le_add
          (mul_le_mul hphaseDerivative htail.2 htail.1.le (by positivity))
          (mul_le_mul hphaseOne htailDerivative (abs_nonneg _) (by norm_num))
  have hqvalue : |rpowRemainderQuotient exponent (ratio ^ depth * realRootTail padding digits ratio)| ≤
      valueBound * upper ^ depth := (hquotient _ hscale).1.trans
        (mul_le_mul_of_nonneg_left hscaleBound hvalue.le)
  constructor
  · unfold realNormalizationError
    rw [abs_mul, abs_of_nonneg hproduct]
    exact (mul_le_mul_of_nonneg_right hproductOne (abs_nonneg _)).trans (by simpa using hqvalue)
  · have hphaseD : HasDerivAt (fun parameter : ℝ => parameter ^ phase)
        (phase * ratio ^ (phase - 1)) ratio := by
      simpa using (hasDerivAt_id ratio).rpow_const (p := phase) (Or.inl hratio.ne')
    have hqD := (differentiableAt_rpowRemainderQuotient exponent hscale).hasDerivAt.comp ratio hscaleD
    have hD : deriv (fun parameter : ℝ =>
        parameter ^ phase * realRootTail padding digits parameter *
          rpowRemainderQuotient exponent
            (parameter ^ depth * realRootTail padding digits parameter)) ratio =
        (phase * ratio ^ (phase - 1) * realRootTail padding digits ratio +
          ratio ^ phase * deriv (realRootTail padding digits) ratio) *
            rpowRemainderQuotient exponent (ratio ^ depth * realRootTail padding digits ratio) +
          (ratio ^ phase * realRootTail padding digits ratio) *
            (deriv (rpowRemainderQuotient exponent)
              (ratio ^ depth * realRootTail padding digits ratio) *
                ((depth : ℝ) * ratio ^ (depth - 1) * realRootTail padding digits ratio +
                  ratio ^ depth * deriv (realRootTail padding digits) ratio)) := by
      simpa only [Pi.mul_apply, Pi.pow_apply, Function.comp_apply, id_eq, mul_one] using!
        ((hphaseD.mul htailD).mul hqD).deriv
    change |deriv (fun parameter => (parameter ^ phase * realRootTail padding digits parameter) *
      rpowRemainderQuotient exponent (parameter ^ depth * realRootTail padding digits parameter)) ratio| ≤ _
    rw [hD]
    calc
      _ ≤ |phase * ratio ^ (phase - 1) * realRootTail padding digits ratio +
          ratio ^ phase * deriv (realRootTail padding digits) ratio| *
          |rpowRemainderQuotient exponent (ratio ^ depth * realRootTail padding digits ratio)| +
          |ratio ^ phase * realRootTail padding digits ratio| *
          (|deriv (rpowRemainderQuotient exponent) (ratio ^ depth * realRootTail padding digits ratio)| *
            |(depth : ℝ) * ratio ^ (depth - 1) * realRootTail padding digits ratio +
              ratio ^ depth * deriv (realRootTail padding digits) ratio|) := by
        simpa only [abs_mul] using
          (abs_add_le
            ((phase * ratio ^ (phase - 1) * realRootTail padding digits ratio +
              ratio ^ phase * deriv (realRootTail padding digits) ratio) *
                rpowRemainderQuotient exponent
                  (ratio ^ depth * realRootTail padding digits ratio))
            ((ratio ^ phase * realRootTail padding digits ratio) *
              (deriv (rpowRemainderQuotient exponent)
                (ratio ^ depth * realRootTail padding digits ratio) *
                  ((depth : ℝ) * ratio ^ (depth - 1) * realRootTail padding digits ratio +
                    ratio ^ depth * deriv (realRootTail padding digits) ratio))))
      _ ≤ (phaseBound / lower + 1) * (valueBound * upper ^ depth) +
          1 * (derivativeBound * ((depth : ℝ) * upper ^ (depth - 1) + upper ^ depth)) :=
        add_le_add (mul_le_mul hproductD hqvalue (abs_nonneg _) (by positivity))
          (mul_le_mul (by simpa only [abs_of_nonneg hproduct] using hproductOne)
            (mul_le_mul (hquotient _ hscale).2 hscaleDerivative (abs_nonneg _) hderivative.le)
            (by positivity) (by norm_num))
      _ = _ := by ring



/-- Uniform control of the phase-times-tail correction in the leading term. -/
theorem real_phase_tail_bounds {lower upper ratio phase phaseBound : ℝ}
    (hlower : 0 < lower) (hlow : lower ≤ ratio) (hhigh : ratio ≤ upper) (hupper : upper < 1)
    (hphase : 0 ≤ phase) (hphaseBound : phase ≤ phaseBound) (padding : ℕ) (digits : ℕ → Bool) :
    |ratio ^ phase * (ratio ^ padding * address ratio digits)| ≤ upper ^ padding ∧
    |deriv (fun parameter : ℝ => parameter ^ phase *
      (parameter ^ padding * address parameter digits)) ratio| ≤
      phaseBound / lower * upper ^ padding +
        ((padding : ℝ) * upper ^ (padding - 1) +
          upper ^ padding * addressParameterDerivativeBound upper) := by
  have hphaseBoundNonnegative : 0 ≤ phaseBound := hphase.trans hphaseBound
  have hratio := lt_of_lt_of_le hlower hlow
  have hlt := lt_of_le_of_lt hhigh hupper
  have hnonnegative := address_nonnegative hratio.le hlt digits
  have hbounded := address_le_one hratio.le hlt digits
  have htail : |ratio ^ padding * address ratio digits| ≤ upper ^ padding := by
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg hratio.le _) hnonnegative)]
    exact (mul_le_of_le_one_right (pow_nonneg hratio.le _) hbounded).trans
      (pow_le_pow_left₀ hratio.le hhigh padding)
  have hphasePower : |ratio ^ phase| ≤ 1 := by
    rw [abs_of_pos (Real.rpow_pos_of_pos hratio _)]
    exact Real.rpow_le_one hratio.le hlt.le hphase
  have hphaseDerivative : |phase * ratio ^ (phase - 1)| ≤ phaseBound / lower := by
    rw [Real.rpow_sub_one hratio.ne', abs_of_nonneg (by positivity)]
    calc
      phase * (ratio ^ phase / ratio) ≤ phaseBound * (1 / lower) := by
        apply mul_le_mul hphaseBound
        · exact div_le_div₀ (by norm_num)
            (Real.rpow_le_one hratio.le hlt.le hphase) hlower hlow
        · positivity
        · exact hphase.trans hphaseBound
      _ = _ := by ring
  constructor
  · rw [abs_mul]
    simpa using mul_le_mul hphasePower htail (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  · have hphaseD : HasDerivAt (fun parameter : ℝ => parameter ^ phase)
        (phase * ratio ^ (phase - 1)) ratio := by
      simpa using (hasDerivAt_id ratio).rpow_const (p := phase) (Or.inl hratio.ne')
    have htailD := (hasDerivAt_scaled_address hratio hlt padding digits).differentiableAt.hasDerivAt
    have hD : deriv (fun parameter : ℝ => parameter ^ phase *
        (parameter ^ padding * address parameter digits)) ratio =
        phase * ratio ^ (phase - 1) * (ratio ^ padding * address ratio digits) +
          ratio ^ phase * deriv
            (fun parameter => parameter ^ padding * address parameter digits) ratio := by
      simpa only [Pi.mul_apply] using! (hphaseD.mul htailD).deriv
    rw [hD]
    calc
      _ ≤ |phase * ratio ^ (phase - 1)| * |ratio ^ padding * address ratio digits| +
          |ratio ^ phase| * |deriv (fun parameter => parameter ^ padding * address parameter digits) ratio| := by
        simpa only [abs_mul] using
          (abs_add_le
            (phase * ratio ^ (phase - 1) * (ratio ^ padding * address ratio digits))
            (ratio ^ phase * deriv
              (fun parameter => parameter ^ padding * address parameter digits) ratio))
      _ ≤ _ := by
        simpa only [one_mul] using add_le_add
          (mul_le_mul hphaseDerivative htail (abs_nonneg _) (by positivity))
          (mul_le_mul hphasePower (scaled_address_derivative_bound hratio hhigh hupper padding digits)
            (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))

end LambdaCantor

