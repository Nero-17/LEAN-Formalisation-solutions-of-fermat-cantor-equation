import Mathlib.Analysis.Real.OfDigits
import Mathlib.Data.Rat.Cast.Order

/-!
# Authorized external black boxes: classical positional-expansion theorem

These are declared axioms, not Lean-proved results. The user explicitly authorized
well-known external theorems as black boxes. They state general positional facts;
they do not assume any conclusion specific to the paper's Cantor-circle problem.

Source: Adamczewski--Frougny--Siegel--Steiner, "Rational numbers with purely
periodic beta-expansion", Introduction, p.1, referring to Hardy--Wright.
https://www.irif.fr/~steiner/AFSS.pdf
The source explicitly states eventual periodicity iff rationality, and pure
periodicity iff the reduced denominator is coprime to the integer base.
For arbitrary positional representations the sole terminating/repeating-maximal
digit ambiguity does not change eventual periodicity. In the second statement,
the interior and coprimality assumptions exclude that ambiguity.
-/

noncomputable section
namespace LambdaCantor.External

/-- The classical rationality criterion for eventually periodic positional digits.
AUTHORIZED EXTERNAL AXIOM; see the module header and EXTERNAL_THEOREMS.md. -/
axiom rational_of_eventually_periodic_digits {base : ℕ} (base_ge_two : 2 ≤ base)
    (digits : ℕ → Fin base)
    (periodic : ∃ start period : ℕ, 0 < period ∧
      ∀ j ≥ start, digits (j + period) = digits j) :
    ∃ rational : ℚ, (rational : ℝ) = Real.ofDigits digits

/-- Pure periodicity for reduced denominators coprime to the base.
AUTHORIZED EXTERNAL AXIOM; the digits are a full base-b expansion in (0,1). -/
axiom periodic_digits_of_coprime_denominator {base : ℕ} (base_ge_two : 2 ≤ base)
    (rational : ℚ) (positive : 0 < rational) (less_one : rational < 1)
    (coprime : Nat.Coprime rational.den base)
    (digits : ℕ → Fin base) (represents : Real.ofDigits digits = (rational : ℝ)) :
    ∃ period : ℕ, 0 < period ∧ ∀ j, digits (j + period) = digits j

end LambdaCantor.External
