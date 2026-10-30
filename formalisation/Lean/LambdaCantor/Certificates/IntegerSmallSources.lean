import Mathlib.Data.Nat.Basic

namespace LambdaCantor.Integer

/-- Padded ternary digits are all zero or two, including an exact width check. -/
def ternaryPrefix : ℕ → ℕ → Bool
  | word, 0 => word == 0
  | word, depth+1 =>
      (word % 3 == 0 || word % 3 == 2) && ternaryPrefix (word/3) depth

/-- Direct finite sources for the exact Fermat equation. The last two
inequalities put the complete derivative-ratio interval strictly inside the
third certified band (89/57,171/89), after positive denominators are cleared.
No logarithm enclosure is needed for these three low exponents. -/
def DirectFermatSource (n P Q p q : ℕ) : Prop :=
  2 ≤ n ∧ 0 < P ∧ 0 < Q ∧ p ≤ q ∧
  ternaryPrefix P p = true ∧ ternaryPrefix Q q = true ∧
  P+1 ≤ 3^p ∧ Q+1 ≤ 3^q ∧
  3^(n*(q-p))*P^n + Q^n < 3^(n*q) ∧
  3^(n*q) < 3^(n*(q-p))*(P+1)^n + (Q+1)^n ∧
  89 * 3^(n*(q-p)) * (P+1)^(n-1) < 57 * Q^(n-1) ∧
  89 * (Q+1)^(n-1) < 171 * 3^(n*(q-p)) * P^(n-1)

instance (n P Q p q : ℕ) : Decidable (DirectFermatSource n P Q p q) := by
  unfold DirectFermatSource
  infer_instance

/-- Exact companion data: r003_parent_elementary_sources.json, n=3. -/
theorem cubic_direct_source : DirectFermatSource 3 54 72 4 4 := by decide +kernel

/-- Exact companion data: r003_parent_elementary_sources.json, n=4. -/
theorem quartic_direct_source : DirectFermatSource 4 180 222 5 5 := by decide +kernel

/-- Exact companion data: r003_parent_elementary_sources.json, n=5. -/
theorem quintic_direct_source : DirectFermatSource 5 648 177066 7 11 := by decide +kernel

end LambdaCantor.Integer
