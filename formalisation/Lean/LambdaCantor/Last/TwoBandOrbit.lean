import LambdaCantor.Last.TwoBandSlopes

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

/-- The offset of one affine child in the order 00,10,01,11. -/
def affineChildOffset (ratio slope : ℝ) (digit : Bool × Bool) : ℝ :=
  (1 - ratio) * ((if digit.1 then 1 else 0) + slope * (if digit.2 then 1 else 0))

/-- Closed regions where a level can have only one strict child interior. -/
def AffineExclusiveRegion (ratio slope level : ℝ) (digit : Bool × Bool) : Prop :=
  match digit with
  | (false, false) => level ≤ 1 - ratio
  | (true, false) => ratio * (1 + slope) ≤ level ∧ level ≤ slope * (1 - ratio)
  | (false, true) => 1 + ratio * slope ≤ level ∧ level ≤ (1 - ratio) * (1 + slope)
  | (true, true) => ratio + slope ≤ level

/-- The entire no-overlap transition graph follows from two strict comparisons.
This lemma is independent of any choice of addresses or limiting argument. -/
theorem affine_exclusive_transition {ratio slope level nextLevel : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (bands : TwoBandSlopes ratio slope) (digit nextDigit : Bool × Bool)
    (hlevel : AffineExclusiveRegion ratio slope level digit)
    (hnext : AffineExclusiveRegion ratio slope nextLevel nextDigit)
    (hrecurrence : level = affineChildOffset ratio slope digit + ratio * nextLevel) :
    (digit = (true, false) → nextDigit = (true, false)) ∧
    (digit = (false, true) → nextDigit = (false, true)) ∧
    (digit = (false, false) → nextDigit ≠ (true, true)) ∧
    (digit = (true, true) → nextDigit ≠ (false, false)) := by
  have hbounds := bands.common_inequalities hpositive hhalf
  have hslope : 0 < slope := by linarith [bands.1]
  rcases digit with ⟨first, second⟩
  rcases nextDigit with ⟨nextFirst, nextSecond⟩
  cases first <;> cases second <;> cases nextFirst <;> cases nextSecond <;>
    simp_all [AffineExclusiveRegion, affineChildOffset] <;>
    nlinarith [mul_pos hpositive hslope]

/-- A bounded orbit with one fixed child digit is its affine fixed point. -/
theorem bounded_affine_orbit_fixed {ratio bound fixed : ℝ}
    (hpositive : 0 < ratio) (hless : ratio < 1) (hbound : 0 ≤ bound)
    (orbit : ℕ → ℝ) (hbounded : ∀ depth, |orbit depth - fixed| ≤ bound)
    (hrecurrence : ∀ depth, orbit depth - fixed = ratio * (orbit (depth + 1) - fixed)) :
    orbit 0 = fixed := by
  have hidentity : ∀ depth, orbit 0 - fixed = ratio ^ depth * (orbit depth - fixed) := by
    intro depth
    induction depth with
    | zero => simp
    | succ depth ih =>
      rw [ih, hrecurrence depth, pow_succ]
      ring
  have hestimate : ∀ depth, |orbit 0 - fixed| ≤ ratio ^ depth * bound := by
    intro depth
    rw [hidentity depth, abs_mul, abs_of_nonneg (pow_nonneg hpositive.le _)]
    exact mul_le_mul_of_nonneg_left (hbounded depth) (pow_nonneg hpositive.le _)
  have hlimit : Tendsto (fun depth : ℕ => ratio ^ depth * bound) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hpositive.le hless).mul_const bound
  have habsolute : |orbit 0 - fixed| ≤ 0 := ge_of_tendsto' hlimit hestimate
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm habsolute (abs_nonneg _)))

/-- An infinite bounded address avoiding every strict overlap is an extreme level.
The middle symbols are absorbing; the two bands exclude their fixed points. -/
theorem two_band_exclusive_orbit_extreme {ratio slope : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (bands : TwoBandSlopes ratio slope) (orbit : ℕ → ℝ) (digits : ℕ → Bool × Bool)
    (hbounded : ∀ depth, 0 ≤ orbit depth ∧ orbit depth ≤ 1 + slope)
    (hexclusive : ∀ depth, AffineExclusiveRegion ratio slope (orbit depth) (digits depth))
    (hrecurrence : ∀ depth,
      orbit depth = affineChildOffset ratio slope (digits depth) + ratio * orbit (depth + 1)) :
    orbit 0 = 0 ∨ orbit 0 = 1 + slope := by
  have hslope : 0 < slope := by linarith [bands.1]
  have hless : ratio < 1 := by linarith
  have htransition := fun depth => affine_exclusive_transition hpositive hhalf bands
    (digits depth) (digits (depth + 1)) (hexclusive depth) (hexclusive (depth + 1))
    (hrecurrence depth)
  have hnot_middle : ∀ depth, digits depth ≠ (true, false) ∧ digits depth ≠ (false, true) := by
    intro depth
    constructor
    · intro hmiddle
      have hconstant : ∀ later, digits (depth + later) = (true, false) := by
        intro later
        induction later with
        | zero => simpa using hmiddle
        | succ later ih => exact (htransition (depth + later)).1 ih
      have hfixed : orbit depth = 1 := by
        have hresult := bounded_affine_orbit_fixed (fixed := 1) hpositive hless (show 0 ≤ 2 + slope by linarith)
          (fun later => orbit (depth + later))
          (fun later => (abs_le.mpr ⟨by linarith [(hbounded (depth + later)).1],
            by linarith [(hbounded (depth + later)).2]⟩))
          (fun later => by
            have hstep := hrecurrence (depth + later)
            rw [hconstant later] at hstep
            simp [affineChildOffset] at hstep
            simp only [Nat.add_assoc] at hstep ⊢
            nlinarith)
        simpa using hresult
      have hregion := hexclusive depth
      rw [hmiddle, hfixed] at hregion
      exact bands.excludes_middle_fixed hpositive hhalf hregion
    · intro hmiddle
      have hconstant : ∀ later, digits (depth + later) = (false, true) := by
        intro later
        induction later with
        | zero => simpa using hmiddle
        | succ later ih => exact (htransition (depth + later)).2.1 ih
      have hfixed : orbit depth = slope := by
        have hresult := bounded_affine_orbit_fixed (fixed := slope) hpositive hless (show 0 ≤ 1 + 2 * slope by linarith)
          (fun later => orbit (depth + later))
          (fun later => (abs_le.mpr ⟨by linarith [(hbounded (depth + later)).1],
            by linarith [(hbounded (depth + later)).2]⟩))
          (fun later => by
            have hstep := hrecurrence (depth + later)
            rw [hconstant later] at hstep
            simp [affineChildOffset] at hstep
            simp only [Nat.add_assoc] at hstep ⊢
            nlinarith)
        simpa using hresult
      have hregion := hexclusive depth
      rw [hmiddle, hfixed] at hregion
      change 1 + ratio * slope ≤ slope ∧ slope ≤ (1 - ratio) * (1 + slope) at hregion
      apply bands.excludes_middle_fixed hpositive hhalf
      constructor <;> nlinarith [hregion.1, hregion.2]
  have hconstant : ∀ depth, digits depth = digits 0 := by
    intro depth
    induction depth with
    | zero => rfl
    | succ depth ih =>
      have hprevious := hnot_middle depth
      have hnext := hnot_middle (depth + 1)
      have hstep := htransition depth
      have hsame : digits (depth + 1) = digits depth := by
        rcases hdigit : digits depth with ⟨first, second⟩
        rcases hnextDigit : digits (depth + 1) with ⟨nextFirst, nextSecond⟩
        cases first <;> cases second <;> cases nextFirst <;> cases nextSecond <;>
          simp [hdigit, hnextDigit] at hprevious hnext hstep ⊢
      exact hsame.trans ih
  rcases hdigit : digits 0 with ⟨first, second⟩
  have hmiddle := hnot_middle 0
  cases first <;> cases second
  · left
    apply bounded_affine_orbit_fixed hpositive hless (show 0 ≤ 1 + slope by linarith) orbit
    · intro depth
      simpa [abs_of_nonneg (hbounded depth).1] using (hbounded depth).2
    · intro depth
      have hstep := hrecurrence depth
      rw [hconstant depth, hdigit] at hstep
      simpa [affineChildOffset] using hstep
  · exact (hmiddle.2 hdigit).elim
  · exact (hmiddle.1 hdigit).elim
  · right
    apply bounded_affine_orbit_fixed hpositive hless (show 0 ≤ 1 + slope by linarith) orbit
    · intro depth
      apply abs_le.mpr
      constructor <;> linarith [(hbounded depth).1, (hbounded depth).2]
    · intro depth
      have hstep := hrecurrence depth
      rw [hconstant depth, hdigit] at hstep
      simp only [affineChildOffset, ite_true, mul_one] at hstep
      nlinarith

end LambdaCantor.Last

