import LambdaCantor.Last.IrrationalRescaling
import Mathlib.NumberTheory.Real.Irrational

noncomputable section
namespace LambdaCantor.Last
open Filter
open scoped Topology

/-- Every positive real exponent has escaping natural depth pairs whose
phase tends to zero. Rational exponents use exact denominator multiples. -/
theorem real_zero_phase_depth_sequences {exponent : ℝ} (hpositive : 0 < exponent) :
    ∃ first second : ℕ → ℕ,
      Tendsto first atTop atTop ∧ Tendsto second atTop atTop ∧
      Tendsto (fun index => (second index : ℝ) - exponent * first index) atTop (𝓝 0) := by
  by_cases hirrational : Irrational exponent
  · exact irrational_depth_sequences hirrational hpositive 0
  · obtain ⟨rational, hrational⟩ := exists_rat_of_not_irrational hirrational
    have hrational_positive : 0 < rational := by exact_mod_cast (hrational ▸ hpositive)
    have hnum : 0 < rational.num := Rat.num_pos.mpr hrational_positive
    have hnum_nat : 0 < rational.num.toNat := by omega
    have hden : 0 < rational.den := rational.pos
    let first : ℕ → ℕ := fun index => rational.den * (index + 1)
    let second : ℕ → ℕ := fun index => rational.num.toNat * (index + 1)
    have hfirst : ∀ index, index ≤ first index := by
      intro index
      dsimp [first]
      nlinarith
    have hsecond : ∀ index, index ≤ second index := by
      intro index
      dsimp [second]
      nlinarith
    refine ⟨first, second, tendsto_atTop_mono hfirst tendsto_id,
      tendsto_atTop_mono hsecond tendsto_id, ?_⟩
    have hphase : (fun index => (second index : ℝ) - exponent * first index) = fun _ => 0 := by
      funext index
      have hnum_cast : (rational.num.toNat : ℝ) = rational.num := by
        exact_mod_cast Int.toNat_of_nonneg hnum.le
      simp only [first, second, Nat.cast_mul, Nat.cast_add, Nat.cast_one, hnum_cast, hrational]
      rw [Rat.cast_def]
      field_simp [ne_of_gt (show (0 : ℝ) < rational.den by exact_mod_cast hden)]
      <;> ring
    rw [hphase]
    exact tendsto_const_nhds

/-- A fixed integer/real endpoint phase can be added to escaping zero-phase
depths. This coefficient statement is valid for every real exponent above one. -/
theorem real_endpoint_coefficient_sequences {exponent ratio : ℝ}
    (hexponent : 0 < exponent) (hpositive : 0 < ratio) (hless : ratio < 1)
    (firstOffset secondOffset : ℕ) :
    ∃ first second : ℕ → ℕ,
      Tendsto first atTop atTop ∧ Tendsto second atTop atTop ∧
      Tendsto (fun index => ratio ^ second index) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun index => exponent * ratio ^ second index / (ratio ^ first index) ^ exponent)
        atTop (𝓝 (exponent * ratio ^ ((secondOffset : ℝ) - exponent * firstOffset))) := by
  obtain ⟨first, second, hfirst, hsecond, hphase⟩ := real_zero_phase_depth_sequences hexponent
  let firstShifted : ℕ → ℕ := fun index => firstOffset + first index
  let secondShifted : ℕ → ℕ := fun index => secondOffset + second index
  have hfirstShifted : Tendsto firstShifted atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_add_left _ _) hfirst
  have hsecondShifted : Tendsto secondShifted atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_add_left _ _) hsecond
  refine ⟨firstShifted, secondShifted, hfirstShifted, hsecondShifted,
    (tendsto_pow_atTop_nhds_zero_of_lt_one hpositive.le hless).comp hsecondShifted, ?_⟩
  have hshifted_phase : Tendsto
      (fun index => (secondShifted index : ℝ) - exponent * firstShifted index) atTop
      (𝓝 ((secondOffset : ℝ) - exponent * firstOffset)) := by
    have hidentity : (fun index => (secondShifted index : ℝ) - exponent * firstShifted index) =
        fun index => ((secondOffset : ℝ) - exponent * firstOffset) +
          ((second index : ℝ) - exponent * first index) := by
      funext index
      simp only [firstShifted, secondShifted, Nat.cast_add]
      ring
    rw [hidentity]
    simpa only [add_zero] using
      (tendsto_const_nhds (x := (secondOffset : ℝ) - exponent * firstOffset)).add hphase
  have hcoefficient : Tendsto
      (fun index => exponent * ratio ^ ((secondShifted index : ℝ) - exponent * firstShifted index)) atTop
      (𝓝 (exponent * ratio ^ ((secondOffset : ℝ) - exponent * firstOffset))) := tendsto_const_nhds.mul
    ((Real.continuous_const_rpow hpositive.ne').continuousAt.tendsto.comp hshifted_phase)
  convert hcoefficient using 1
  funext index
  rw [Real.rpow_sub hpositive, Real.rpow_natCast,
    show exponent * (firstShifted index : ℝ) = (firstShifted index : ℝ) * exponent by ring,
    Real.rpow_mul hpositive.le, Real.rpow_natCast]
  exact mul_div_assoc _ _ _

/-- The endpoint phase allows an arbitrary integer second offset. A finite
tail makes the corresponding actual Cantor depth nonnegative. -/
theorem real_integer_endpoint_coefficient_sequences {exponent ratio : ℝ}
    (hexponent : 0 < exponent) (hpositive : 0 < ratio) (hless : ratio < 1)
    (firstOffset : ℕ) (secondOffset : ℤ) :
    ∃ first second : ℕ → ℕ,
      Tendsto first atTop atTop ∧ Tendsto second atTop atTop ∧
      Tendsto (fun index => ratio ^ second index) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun index => exponent * ratio ^ second index / (ratio ^ first index) ^ exponent)
        atTop (𝓝 (exponent * ratio ^ ((secondOffset : ℝ) - exponent * firstOffset))) := by
  obtain ⟨first, second, hfirst, hsecond, hphase⟩ := real_zero_phase_depth_sequences hexponent
  obtain ⟨offsetBound, hoffsetBound⟩ := exists_nat_gt (-secondOffset)
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.mp
    (hsecond.eventually (eventually_ge_atTop offsetBound))
  let firstShifted : ℕ → ℕ := fun index => firstOffset + first (index + cutoff)
  let secondShifted : ℕ → ℕ := fun index => (secondOffset + (second (index + cutoff) : ℤ)).toNat
  have hsecond_nonnegative : ∀ index, 0 ≤ secondOffset + (second (index + cutoff) : ℤ) := by
    intro index
    have hlarge := hcutoff (index + cutoff) (by omega)
    omega
  have hsecond_cast : ∀ index, (secondShifted index : ℝ) =
      (secondOffset : ℝ) + second (index + cutoff) := by
    intro index
    dsimp [secondShifted]
    have hcast : (((secondOffset + (second (index + cutoff) : ℤ)).toNat : ℕ) : ℝ) =
        ((secondOffset + (second (index + cutoff) : ℤ)) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (hsecond_nonnegative index)
    simpa only [Int.cast_add, Int.cast_natCast] using hcast
  have htail : Tendsto (fun index : ℕ => index + cutoff) atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_add_right _ _) tendsto_id
  have hfirstShifted : Tendsto firstShifted atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_add_left _ _) (hfirst.comp htail)
  have hsecondShifted_real : Tendsto (fun index => (secondShifted index : ℝ)) atTop atTop := by
    simp only [hsecond_cast]
    exact tendsto_const_nhds.add_atTop ((tendsto_natCast_atTop_atTop.comp hsecond).comp htail)
  have hsecondShifted : Tendsto secondShifted atTop atTop :=
    tendsto_natCast_atTop_iff.mp hsecondShifted_real
  refine ⟨firstShifted, secondShifted, hfirstShifted, hsecondShifted,
    (tendsto_pow_atTop_nhds_zero_of_lt_one hpositive.le hless).comp hsecondShifted, ?_⟩
  have hshifted_phase : Tendsto
      (fun index => (secondShifted index : ℝ) - exponent * firstShifted index) atTop
      (𝓝 ((secondOffset : ℝ) - exponent * firstOffset)) := by
    have hidentity : (fun index => (secondShifted index : ℝ) - exponent * firstShifted index) =
        fun index => ((secondOffset : ℝ) - exponent * firstOffset) +
          ((second (index + cutoff) : ℝ) - exponent * first (index + cutoff)) := by
      funext index
      simp only [firstShifted, hsecond_cast, Nat.cast_add]
      ring
    rw [hidentity]
    simpa only [add_zero, Function.comp_apply] using
      (tendsto_const_nhds (x := (secondOffset : ℝ) - exponent * firstOffset)).add (hphase.comp htail)
  have hcoefficient : Tendsto
      (fun index => exponent * ratio ^ ((secondShifted index : ℝ) - exponent * firstShifted index)) atTop
      (𝓝 (exponent * ratio ^ ((secondOffset : ℝ) - exponent * firstOffset))) := tendsto_const_nhds.mul
    ((Real.continuous_const_rpow hpositive.ne').continuousAt.tendsto.comp hshifted_phase)
  convert hcoefficient using 1
  funext index
  rw [Real.rpow_sub hpositive, Real.rpow_natCast,
    show exponent * (firstShifted index : ℝ) = (firstShifted index : ℝ) * exponent by ring,
    Real.rpow_mul hpositive.le, Real.rpow_natCast]
  exact mul_div_assoc _ _ _

end LambdaCantor.Last
