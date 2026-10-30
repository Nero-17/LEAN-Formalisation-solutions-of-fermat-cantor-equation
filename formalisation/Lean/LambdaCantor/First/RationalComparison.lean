import Mathlib.Topology.Order.IntermediateValue
import LambdaCantor.First.RationalEstimates
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
namespace LambdaCantor.First

/-- Comparison function in the denominator theorem, with real powers. -/
def rationalComparison (exponent phase ratio : ℝ) : ℝ :=
  (1 - ratio) ^ exponent - exponent * ratio ^ phase

/-- Exact derivative of the rational comparison function on the parameter
interval. -/
theorem hasDerivAt_rationalComparison (exponent phase ratio : ℝ)
    (hratio : 0 < ratio) (hone : ratio < 1) :
    HasDerivAt (rationalComparison exponent phase)
      (-exponent * (1 - ratio) ^ (exponent - 1) -
        exponent * phase * ratio ^ (phase - 1)) ratio := by
  have hfirst := ((hasDerivAt_const ratio (1 : ℝ)).sub (hasDerivAt_id ratio)).rpow_const
    (p := exponent) (Or.inl (by dsimp; linarith))
  have hsecond := ((hasDerivAt_id ratio).rpow_const
    (p := phase) (Or.inl (ne_of_gt hratio))).const_mul exponent
  convert! hfirst.sub hsecond using 1 <;> dsimp only [rationalComparison, Pi.sub_apply, Pi.mul_apply, id_eq] <;> ring

/-- Shifting the phase rewrites the left endpoint exactly as an exponential
loss, making the lattice error estimate applicable. -/
theorem comparison_quarter_rewrite {exponent phase target : ℝ}
    (hbalance : exponent * (1 / 4 : ℝ) ^ target = (3 / 4 : ℝ) ^ exponent) :
    rationalComparison exponent phase (1 / 4) =
      (3 / 4 : ℝ) ^ exponent *
        (1 - Real.exp (-((phase - target) * Real.log 4))) := by
  have hlog : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    rw [one_div, Real.log_inv]
  have hsplit : (1 / 4 : ℝ) ^ phase = (1 / 4 : ℝ) ^ target *
      Real.exp (-((phase - target) * Real.log 4)) := by
    calc
      (1 / 4 : ℝ) ^ phase = (1 / 4 : ℝ) ^ (target + (phase - target)) := by congr 1; ring
      _ = (1 / 4 : ℝ) ^ target * (1 / 4 : ℝ) ^ (phase - target) :=
        Real.rpow_add (by norm_num) _ _
      _ = _ := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 4) (phase - target), hlog]
        congr 2 <;> ring
  unfold rationalComparison
  norm_num only [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num]
  rw [hsplit, ← mul_assoc, hbalance]
  ring

/-- The exact endpoint upper bound in the denominator proof. -/
theorem comparison_quarter_error {exponent phase target denominator : ℝ}
    (hbalance : exponent * (1 / 4 : ℝ) ^ target = (3 / 4 : ℝ) ^ exponent)
    (hstep : phase - target ≤ 1 / denominator) :
    rationalComparison exponent phase (1 / 4) ≤
      (3 / 4 : ℝ) ^ exponent * Real.log 4 / denominator := by
  rw [comparison_quarter_rewrite hbalance]
  calc
    (3 / 4 : ℝ) ^ exponent * (1 - Real.exp (-((phase - target) * Real.log 4))) ≤
        (3 / 4 : ℝ) ^ exponent * ((1 / denominator) * Real.log 4) :=
      exponential_lattice_error (Real.rpow_nonneg (by norm_num) _)
        (mul_le_mul_of_nonneg_right hstep (Real.log_pos (by norm_num)).le)
    _ = _ := by ring

/-- The phase chosen in the denominator proof balances the comparison at
one quarter exactly. -/
theorem comparison_balance_phase {exponent : ℝ} (hexponent : 0 < exponent) :
    exponent * (1 / 4 : ℝ) ^
      ((exponent * Real.log (4 / 3) + Real.log exponent) / Real.log 4) =
        (3 / 4 : ℝ) ^ exponent := by
  have hlog4 : Real.log 4 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlogquarter : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    rw [one_div, Real.log_inv]
  have hlogratio : Real.log (4 / 3 : ℝ) = -Real.log (3 / 4 : ℝ) := by
    rw [show (4 / 3 : ℝ) = (3 / 4 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hargument : Real.log (1 / 4 : ℝ) *
      ((exponent * Real.log (4 / 3) + Real.log exponent) / Real.log 4) =
        Real.log (3 / 4 : ℝ) * exponent - Real.log exponent := by
    rw [hlogquarter, hlogratio]
    field_simp [hlog4]
    <;> ring
  rw [Real.rpow_def_of_pos (by norm_num), hargument, Real.exp_sub,
    Real.exp_log hexponent, Real.rpow_def_of_pos (by norm_num)]
  field_simp [ne_of_gt hexponent]

/-- Uniform negative-slope bound on the whole comparison interval. -/
theorem rationalComparison_derivative_le {exponent phase ratio : ℝ}
    (hexponent : 2 ≤ exponent) (hphase : 0 ≤ phase)
    (hratio : ratio ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    deriv (rationalComparison exponent phase) ratio ≤
      -(exponent * (2 : ℝ) ^ (1 - exponent)) := by
  rw [(hasDerivAt_rationalComparison exponent phase ratio
    (by linarith [hratio.1]) (by linarith [hratio.2])).deriv]
  have hpower : (1 / 2 : ℝ) ^ (exponent - 1) ≤ (1 - ratio) ^ (exponent - 1) :=
    Real.rpow_le_rpow (by norm_num) (by linarith [hratio.2]) (by linarith)
  have hhalf : (1 / 2 : ℝ) ^ (exponent - 1) = (2 : ℝ) ^ (1 - exponent) := by
    rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  rw [hhalf] at hpower
  have hscaled := mul_le_mul_of_nonneg_left hpower (by linarith : 0 ≤ exponent)
  have htail : 0 ≤ exponent * phase * ratio ^ (phase - 1) := by
    apply mul_nonneg (mul_nonneg (by linarith) hphase)
    exact Real.rpow_nonneg (by linarith [hratio.1]) _
  linarith

/-- Positivity of the balancing phase for all exponents in the paper. -/
theorem comparison_balance_phase_pos {exponent : ℝ} (hexponent : 2 ≤ exponent) :
    0 < (exponent * Real.log (4 / 3) + Real.log exponent) / Real.log 4 := by
  apply div_pos _ (Real.log_pos (by norm_num))
  apply add_pos
  · exact mul_pos (by linarith) (Real.log_pos (by norm_num))
  · exact Real.log_pos (by linarith)

/-- The next phase at distance at most one from the balancing phase is
still below the phase at which the half-endpoint comparison changes sign. -/
theorem comparison_phase_ceiling_lt {exponent : ℝ} (hexponent : 2 ≤ exponent) :
    (exponent * Real.log (4 / 3) + Real.log exponent) / Real.log 4 + 1 <
      exponent + Real.log exponent / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  have hlog43 : Real.log (4 / 3 : ℝ) = Real.log 4 - Real.log 3 :=
    Real.log_div (by norm_num) (by norm_num)
  have hlogExponent : 0 < Real.log exponent := Real.log_pos (by linarith)
  have hscaled := mul_le_mul_of_nonneg_right hexponent hlog3.le
  have hstrict : Real.log 4 < exponent * Real.log 3 + Real.log exponent := by
    nlinarith
  suffices hquotient : (exponent * Real.log (4 / 3) + Real.log exponent) / Real.log 4 <
      exponent + Real.log exponent / Real.log 2 - 1 by linarith
  apply (div_lt_iff₀ hlog4).mpr
  have hright : (exponent + Real.log exponent / Real.log 2 - 1) * Real.log 4 =
      exponent * Real.log 4 + 2 * Real.log exponent - Real.log 4 := by
    rw [hlog4eq]
    field_simp [ne_of_gt hlog2]
    <;> ring
  rw [hright, hlog43]
  nlinarith

/-- Strict sign at the right endpoint, with the exact phase range used in
the denominator construction. -/
theorem rationalComparison_half_neg {exponent phase : ℝ}
    (hexponent : 2 ≤ exponent)
    (hphase : phase ≤ (exponent * Real.log (4 / 3) + Real.log exponent) / Real.log 4 + 1) :
    rationalComparison exponent phase (1 / 2) < 0 := by
  have hphaseBound := hphase.trans_lt (comparison_phase_ceiling_lt hexponent)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbound : (phase - exponent) * Real.log 2 < Real.log exponent :=
    (lt_div_iff₀ hlog2).mp (by linarith)
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  unfold rationalComparison
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  apply sub_neg.mpr
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2) exponent,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2) phase]
  calc
    Real.exp (Real.log (1 / 2) * exponent) <
        Real.exp (Real.log exponent + Real.log (1 / 2) * phase) := by
      apply Real.exp_lt_exp.mpr
      rw [hloghalf]
      nlinarith
    _ = exponent * Real.exp (Real.log (1 / 2) * phase) := by
      rw [Real.exp_add, Real.exp_log (by linarith : 0 < exponent)]

/-- Strict sign at the left endpoint for a phase strictly above balance. -/
theorem rationalComparison_quarter_pos {exponent phase : ℝ}
    (hexponent : 2 ≤ exponent)
    (hphase : (exponent * Real.log (4 / 3) + Real.log exponent) / Real.log 4 < phase) :
    0 < rationalComparison exponent phase (1 / 4) := by
  rw [comparison_quarter_rewrite (comparison_balance_phase (by linarith : 0 < exponent))]
  apply mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have := mul_pos (sub_pos.mpr hphase) hlog4
  linarith

/-- Existence and uniqueness of the scalar transverse comparison root for
every phase selected by the denominator construction. This theorem has no
root-existence or endpoint-sign hypotheses. -/
theorem exists_unique_rationalComparison_root {exponent phase : ℝ}
    (hexponent : 2 ≤ exponent)
    (hphaseLower : (exponent * Real.log (4 / 3) + Real.log exponent) / Real.log 4 < phase)
    (hphaseUpper : phase ≤ (exponent * Real.log (4 / 3) + Real.log exponent) / Real.log 4 + 1) :
    ∃! ratio : ℝ, ratio ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∧
      rationalComparison exponent phase ratio = 0 := by
  have hphase : 0 < phase := (comparison_balance_phase_pos hexponent).trans hphaseLower
  have hleft := rationalComparison_quarter_pos hexponent hphaseLower
  have hright := rationalComparison_half_neg hexponent hphaseUpper
  have hcontinuous : ContinuousOn (rationalComparison exponent phase)
      (Set.Icc (1 / 4 : ℝ) (1 / 2)) := by
    intro ratio hratio
    exact (hasDerivAt_rationalComparison exponent phase ratio
      (by linarith [hratio.1]) (by linarith [hratio.2])).continuousAt.continuousWithinAt
  obtain ⟨ratio, hratio, hzero⟩ := intermediate_value_Icc'
    (show (1 / 4 : ℝ) ≤ 1 / 2 by norm_num) hcontinuous ⟨hright.le, hleft.le⟩
  have hstrict : ratio ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) := by
    constructor
    · by_contra hnot
      have heq : ratio = 1 / 4 := le_antisymm (le_of_not_gt hnot) hratio.1
      rw [heq] at hzero
      linarith
    · by_contra hnot
      have heq : ratio = 1 / 2 := le_antisymm hratio.2 (le_of_not_gt hnot)
      rw [heq] at hzero
      linarith
  have hslope : 0 < exponent * (2 : ℝ) ^ (1 - exponent) := by positivity
  have hanti := LambdaCantor.strictAntiOn_of_uniform_negative_derivative hcontinuous hslope
    (fun parameter hparameter => rationalComparison_derivative_le hexponent hphase.le
      ⟨hparameter.1.le, hparameter.2.le⟩)
  refine ⟨ratio, ⟨hstrict, hzero⟩, ?_⟩
  intro other hother
  exact hanti.injOn ⟨hother.1.1.le, hother.1.2.le⟩ hratio (hother.2.trans hzero.symm)

end LambdaCantor.First







