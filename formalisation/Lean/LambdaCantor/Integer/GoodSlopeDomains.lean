import LambdaCantor.Classical.Periodicity
import LambdaCantor.Classical.RationalAddress
import LambdaCantor.Integer.GoodSlopes

noncomputable section
namespace LambdaCantor.Integer

/-- The original circle slope band is contained in the first of the five
additional admissible bands. Thus the same interface covers every admissible
interval in the current manuscript. -/
theorem goodSlope_of_classical_band {slope : ℝ}
    (lower : (11 : ℝ)/9 < slope) (upper : slope < 2027/1624) :
    GoodSlope slope := by
  apply Or.inl
  constructor <;> linarith

/-- The analytic recurrence interface to all five certified slope bands. -/
theorem good_slope_domains_eventually_periodic
    (slope : ℝ) (good : GoodSlope slope)
    (digits : ℕ → Fin 4) (tails errors : ℕ → ℝ)
    (nonnegative : ∀ n, 0 ≤ errors n)
    (vanishing : ∀ ε > 0, ∃ start, ∀ n ≥ start, errors n < ε)
    (recurrence : ∀ n, tails (n+1) = 3 * tails n -
      (((digits n).val / 2 : ℕ) : ℝ) * slope - (((digits n).val % 2 : ℕ) : ℝ))
    (lower : ∀ n, ((lowerCoefficient (digits n).val).1 * slope +
      (lowerCoefficient (digits n).val).2) / 6 - errors n ≤ tails n)
    (upper : ∀ n, tails n ≤ ((upperCoefficient (digits n).val).1 * slope +
      (upperCoefficient (digits n).val).2) / 6 + errors n) :
    ∃ start, ∀ n ≥ start, digits (n+4) = digits n := by
  apply good_slopes_eventually_periodic slope good digits
    (fun n => 972 * Classical.windowError errors n)
    (Classical.scaled_windowError_vanishes errors vanishing)
  apply Classical.sequence_approximate_discrepancy digits slope tails errors nonnegative recurrence
  · intro n
    have domain := lower n
    linarith
  · intro n
    have domain := upper n
    linarith

/-- Periodicity of any injective encoding of digit pairs makes both coordinates rational. -/
theorem rational_addresses_of_periodic_labels
    (encode : Bool × Bool → Fin 4) (injective : Function.Injective encode)
    (first second : ℕ → Bool)
    (periodic : ∃ start, ∀ n ≥ start,
      encode (first (n+4), second (n+4)) = encode (first n, second n)) :
    (∃ rational : ℚ, (rational : ℝ) = address (1/3) first) ∧
      (∃ rational : ℚ, (rational : ℝ) = address (1/3) second) := by
  obtain ⟨start, periodic⟩ := periodic
  constructor
  · apply Classical.rational_address_of_eventually_periodic
    exact ⟨start, 4, by omega, fun n large =>
      congrArg Prod.fst (injective (periodic n large))⟩
  · apply Classical.rational_address_of_eventually_periodic
    exact ⟨start, 4, by omega, fun n large =>
      congrArg Prod.snd (injective (periodic n large))⟩

end LambdaCantor.Integer
