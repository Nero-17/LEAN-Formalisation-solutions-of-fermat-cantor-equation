import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

noncomputable section
open Filter
namespace LambdaCantor.First

/-- Every integer phase numerator has a nonnegative lattice solution when
the exponent numerator and denominator are positive and coprime. -/
theorem exists_natural_phase_solution (numerator denominator : ℕ)
    (hnumerator : 0 < numerator) (hdenominator : 0 < denominator)
    (hcoprime : numerator.Coprime denominator) (phaseNumerator : ℤ) :
    ∃ k m : ℕ, (denominator : ℤ) * m - (numerator : ℤ) * k = phaseNumerator := by
  have hbezout : (1 : ℤ) = (numerator : ℤ) * Nat.gcdA numerator denominator +
      (denominator : ℤ) * Nat.gcdB numerator denominator := by
    simpa only [hcoprime.gcd_eq_one, Nat.cast_one] using
      (Nat.gcd_eq_gcd_ab numerator denominator)
  let initialK : ℤ := -phaseNumerator * Nat.gcdA numerator denominator
  let initialM : ℤ := phaseNumerator * Nat.gcdB numerator denominator
  have hphase : (denominator : ℤ) * initialM - (numerator : ℤ) * initialK =
      phaseNumerator := by
    dsimp [initialK, initialM]
    nlinarith [congrArg (fun z : ℤ => phaseNumerator * z) hbezout]
  obtain ⟨shift, hshift⟩ := exists_nat_gt (max (-initialK) (-initialM))
  have hnum : (1 : ℤ) ≤ numerator := by exact_mod_cast (Nat.succ_le_of_lt hnumerator)
  have hden : (1 : ℤ) ≤ denominator := by exact_mod_cast (Nat.succ_le_of_lt hdenominator)
  have hshiftNonneg : (0 : ℤ) ≤ shift := Nat.cast_nonneg _
  have hk : 0 ≤ initialK + (denominator : ℤ) * shift := by
    have := (le_max_left (-initialK) (-initialM)).trans_lt hshift
    nlinarith
  have hm : 0 ≤ initialM + (numerator : ℤ) * shift := by
    have := (le_max_right (-initialK) (-initialM)).trans_lt hshift
    nlinarith
  refine ⟨(initialK + (denominator : ℤ) * shift).toNat,
    (initialM + (numerator : ℤ) * shift).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hk, Int.toNat_of_nonneg hm]
  nlinarith [hphase]

/-- Exact rational phases can be realized along natural cylinder depths
with both depths tending to infinity. -/
theorem rational_phase_sequences (numerator denominator : ℕ)
    (hnumerator : 0 < numerator) (hdenominator : 0 < denominator)
    (hcoprime : numerator.Coprime denominator) (phase : ℝ)
    (hphase : ∃ phaseNumerator : ℤ, (denominator : ℝ) * phase = phaseNumerator) :
    ∃ k m : ℕ → ℕ, Tendsto k atTop atTop ∧ Tendsto m atTop atTop ∧
      ∀ index, (m index : ℝ) - ((numerator : ℝ) / denominator) * k index = phase := by
  obtain ⟨phaseNumerator, hphaseNumerator⟩ := hphase
  obtain ⟨initialK, initialM, hsolution⟩ :=
    exists_natural_phase_solution numerator denominator hnumerator hdenominator
      hcoprime phaseNumerator
  refine ⟨fun index => initialK + denominator * index,
    fun index => initialM + numerator * index, ?_, ?_, ?_⟩
  · apply tendsto_atTop_mono _ tendsto_id
    intro index
    change index ≤ initialK + denominator * index
    exact (Nat.le_mul_of_pos_left index hdenominator).trans
      (Nat.le_add_left (denominator * index) initialK)
  · apply tendsto_atTop_mono _ tendsto_id
    intro index
    change index ≤ initialM + numerator * index
    exact (Nat.le_mul_of_pos_left index hnumerator).trans
      (Nat.le_add_left (numerator * index) initialM)
  · intro index
    have hsolutionReal : (denominator : ℝ) * initialM -
        (numerator : ℝ) * initialK = phaseNumerator := by exact_mod_cast hsolution
    have hden : (denominator : ℝ) ≠ 0 := by positivity
    push_cast
    apply (mul_left_cancel₀ hden)
    field_simp
    nlinarith [hsolutionReal, hphaseNumerator]

end LambdaCantor.First



