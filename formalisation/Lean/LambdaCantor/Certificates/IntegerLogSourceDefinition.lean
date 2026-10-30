import LambdaCantor.Certificates.IntegerSmallSources

namespace LambdaCantor.Integer

/-- The five printed slope bands followed by their reciprocals. Each tuple
contains lower numerator, lower denominator, upper numerator, upper denominator. -/
def logSourceBand : Fin 10 → ℕ × ℕ × ℕ × ℕ
  | ⟨0, _⟩ => (89,73,171,137)
  | ⟨1, _⟩ => (101,79,183,143)
  | ⟨2, _⟩ => (89,57,171,89)
  | ⟨3, _⟩ => (143,61,237,101)
  | ⟨4, _⟩ => (137,57,219,89)
  | ⟨5, _⟩ => (137,171,73,89)
  | ⟨6, _⟩ => (143,183,79,101)
  | ⟨7, _⟩ => (89,171,57,89)
  | ⟨8, _⟩ => (101,237,61,143)
  | _ => (89,219,57,137)

structure LogSourceData where
  d : ℕ
  P : ℕ
  Q : ℕ
  p : ℕ
  q : ℕ
  band : Fin 10

/-- Exact denominator-cleared source predicate for the logarithmic limit.
The corner inequalities compare u^n/(n*v) with 3^(-d). The final two
inequalities enclose the *whole* derivative-ratio interval
[n*Q/(P+1), n*(Q+1)/P] in one of the printed bands or reciprocals.
No floating-point arithmetic, logarithm approximation, or external PASS is used. -/
def LogSourceData.Valid (n : ℕ) (source : LogSourceData) : Prop :=
  3 ≤ n ∧ 0 < source.P ∧ 0 < source.Q ∧
  ternaryPrefix source.P source.p = true ∧
  ternaryPrefix source.Q source.q = true ∧
  source.P + 1 ≤ 3^source.p ∧ source.Q + 1 ≤ 3^source.q ∧
  3^((source.d+source.q)-(source.p*n)) * source.P^n <
    n*(source.Q+1)*3^((source.p*n)-(source.d+source.q)) ∧
  n*source.Q*3^((source.p*n)-(source.d+source.q)) <
    3^((source.d+source.q)-(source.p*n))*(source.P+1)^n ∧
  (logSourceBand source.band).1 * (source.P+1) <
    (logSourceBand source.band).2.1 * n * source.Q ∧
  (logSourceBand source.band).2.2.2 * n * (source.Q+1) <
    (logSourceBand source.band).2.2.1 * source.P

instance (n : ℕ) (source : LogSourceData) : Decidable (source.Valid n) := by
  unfold LogSourceData.Valid
  infer_instance

end LambdaCantor.Integer
