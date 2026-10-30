import LambdaCantor.Last.IrrationalRescaling
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.RationalPowers

/-- Every rational phase is realized at arbitrarily large actual natural
Cantor depths. The congruence is solved by Bezout and then shifted along its
positive solution ray. No integrality of the real exponent is assumed. -/
theorem rational_natural_phase_depths (numerator denominator : ℕ) (phase : ℤ)
    (coprime : numerator.Coprime denominator)
    (numerator_positive : 0 < numerator) (denominator_positive : 0 < denominator)
    (start : ℕ) :
    ∃ first second : ℕ, start ≤ first ∧ start ≤ second ∧
      (second : ℝ) - ((numerator : ℝ)/denominator)*first = (phase : ℝ)/denominator := by
  have bezout : (numerator : ℤ)*Nat.gcdA numerator denominator +
      (denominator : ℤ)*Nat.gcdB numerator denominator = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, coprime.gcd_eq_one]
    norm_num
  let firstBase : ℤ := -phase*Nat.gcdA numerator denominator
  let secondBase : ℤ := phase*Nat.gcdB numerator denominator
  have base_equation : (numerator : ℤ)*firstBase+phase =
      (denominator : ℤ)*secondBase := by
    dsimp [firstBase, secondBase]
    nlinarith [congrArg (fun value : ℤ => phase*value) bezout]
  let offset : ℤ := max 0 (max ((start : ℤ)-firstBase) ((start : ℤ)-secondBase))
  have offset_nonnegative : 0 ≤ offset := le_max_left _ _
  have offset_first : (start : ℤ)-firstBase ≤ offset :=
    (le_max_left _ _).trans (le_max_right _ _)
  have offset_second : (start : ℤ)-secondBase ≤ offset :=
    (le_max_right _ _).trans (le_max_right _ _)
  have numerator_ge_one : (1 : ℤ) ≤ numerator := by
    have positive : (0 : ℤ) < numerator := by exact_mod_cast numerator_positive
    omega
  have denominator_ge_one : (1 : ℤ) ≤ denominator := by
    have positive : (0 : ℤ) < denominator := by exact_mod_cast denominator_positive
    omega
  have first_large : (start : ℤ) ≤ firstBase+denominator*offset := by
    nlinarith [mul_nonneg (sub_nonneg.mpr denominator_ge_one) offset_nonnegative]
  have second_large : (start : ℤ) ≤ secondBase+numerator*offset := by
    nlinarith [mul_nonneg (sub_nonneg.mpr numerator_ge_one) offset_nonnegative]
  have first_nonnegative : 0 ≤ firstBase+denominator*offset :=
    (Int.natCast_nonneg start).trans first_large
  have second_nonnegative : 0 ≤ secondBase+numerator*offset :=
    (Int.natCast_nonneg start).trans second_large
  have first_cast : (((firstBase+denominator*offset).toNat : ℕ) : ℤ) =
      firstBase+denominator*offset := Int.toNat_of_nonneg first_nonnegative
  have second_cast : (((secondBase+numerator*offset).toNat : ℕ) : ℤ) =
      secondBase+numerator*offset := Int.toNat_of_nonneg second_nonnegative
  refine ⟨(firstBase+denominator*offset).toNat,
    (secondBase+numerator*offset).toNat, ?_, ?_, ?_⟩
  · rw [← first_cast] at first_large
    exact_mod_cast first_large
  · rw [← second_cast] at second_large
    exact_mod_cast second_large
  · have integer_equation :
        (denominator : ℤ)*((secondBase+numerator*offset).toNat : ℤ) -
          (numerator : ℤ)*((firstBase+denominator*offset).toNat : ℤ) = phase := by
      rw [first_cast, second_cast]
      nlinarith [base_equation]
    have real_equation :
        (denominator : ℝ)*((secondBase+numerator*offset).toNat : ℝ) -
          (numerator : ℝ)*((firstBase+denominator*offset).toNat : ℝ) = phase := by
      exact_mod_cast integer_equation
    have nonzero : (denominator : ℝ) ≠ 0 := by positivity
    field_simp [nonzero]
    nlinarith [real_equation]

/-- The two actual depths escape together with an exactly fixed rational
phase, supplying the rational analogue of irrational rotation sequences. -/
theorem rational_phase_depth_sequences (numerator denominator : ℕ) (phase : ℤ)
    (coprime : numerator.Coprime denominator)
    (numerator_positive : 0 < numerator) (denominator_positive : 0 < denominator) :
    ∃ first second : ℕ → ℕ,
      Tendsto first atTop atTop ∧ Tendsto second atTop atTop ∧
      ∀ index, (second index : ℝ) - ((numerator : ℝ)/denominator)*first index =
        (phase : ℝ)/denominator := by
  choose first second first_large second_large equation using
    rational_natural_phase_depths numerator denominator phase coprime numerator_positive denominator_positive
  exact ⟨first, second, tendsto_atTop_mono first_large tendsto_id,
    tendsto_atTop_mono second_large tendsto_id, equation⟩

/-- At those depths the actual normalized coefficient is exactly the source
coefficient, while the near-axis scale tends to zero. This removes the old
integer-only depth restriction from the source transfer. -/
theorem rational_actual_source_sequences (numerator denominator : ℕ) (phase : ℤ)
    (coprime : numerator.Coprime denominator)
    (numerator_positive : 0 < numerator) (denominator_positive : 0 < denominator)
    {ratio : ℝ} (ratio_positive : 0 < ratio) (ratio_less_one : ratio < 1) :
    ∃ first second : ℕ → ℕ,
      Tendsto first atTop atTop ∧ Tendsto second atTop atTop ∧
      Tendsto (fun index => ratio^(second index)) atTop (𝓝 (0 : ℝ)) ∧
      ∀ index, ((numerator : ℝ)/denominator)*ratio^(second index)/
          (ratio^(first index))^((numerator : ℝ)/denominator) =
        ((numerator : ℝ)/denominator)*ratio^((phase : ℝ)/denominator) := by
  obtain ⟨first, second, first_limit, second_limit, phases⟩ :=
    rational_phase_depth_sequences numerator denominator phase coprime numerator_positive denominator_positive
  refine ⟨first, second, first_limit, second_limit,
    (tendsto_pow_atTop_nhds_zero_of_lt_one ratio_positive.le ratio_less_one).comp second_limit, ?_⟩
  intro index
  rw [← phases index, Real.rpow_sub ratio_positive, Real.rpow_natCast]
  rw [show ((numerator : ℝ)/denominator)*(first index : ℝ) =
    (first index : ℝ)*((numerator : ℝ)/denominator) by ring,
    Real.rpow_mul ratio_positive.le, Real.rpow_natCast]
  ring

end LambdaCantor.RationalPowers

