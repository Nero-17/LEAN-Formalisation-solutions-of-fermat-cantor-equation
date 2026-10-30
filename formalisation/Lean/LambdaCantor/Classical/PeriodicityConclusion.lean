import LambdaCantor.Classical.Periodicity
import LambdaCantor.Integer.Band0Periodicity
import Mathlib.Topology.MetricSpace.HausdorffDistance

noncomputable section
namespace LambdaCantor.Classical
open LambdaCantor.Integer

/-- The article's original four-label periodicity conclusion, from the exact
recurrence and vanishing perturbations of all four exclusive intervals.
Its finite certificate is the stronger first good-slope band. -/
theorem exclusive_domains_eventually_periodic
    (slope : ℝ) (slope_lower : 11 / 9 < slope) (slope_upper : slope < 2027 / 1624)
    (digits : ℕ → Fin 4) (tails errors : ℕ → ℝ)
    (nonnegative : ∀ n, 0 ≤ errors n)
    (vanishing : ∀ ε > 0, ∃ start, ∀ n ≥ start, errors n < ε)
    (recurrence : ∀ n, tails (n+1) = 3 * tails n -
      (((digits n).val / 2 : ℕ) : ℝ) * slope - (((digits n).val % 2 : ℕ) : ℝ))
    (lower : ∀ n, ((lowerCoefficient (digits n).val).1 * slope +
      (lowerCoefficient (digits n).val).2) / 6 - errors n ≤ tails n)
    (upper : ∀ n, tails n ≤
      ((upperCoefficient (digits n).val).1 * slope +
        (upperCoefficient (digits n).val).2) / 6 + errors n) :
    ∃ start, ∀ n ≥ start, digits (n+4) = digits n := by
  apply original_band_eventually_periodic slope slope_lower slope_upper digits
    (fun n => 972 * windowError errors n)
    (scaled_windowError_vanishes errors vanishing)
  apply sequence_approximate_discrepancy digits slope tails errors nonnegative recurrence
  · intro n
    have domain := lower n
    linarith
  · intro n
    have domain := upper n
    linarith

def exclusiveInterval (slope : ℝ) (digit : Fin 4) : Set ℝ :=
  Set.Icc (((lowerCoefficient digit.val).1 * slope +
    (lowerCoefficient digit.val).2) / 6)
    (((upperCoefficient digit.val).1 * slope + (upperCoefficient digit.val).2) / 6)

theorem exclusiveInterval_nonempty (slope : ℝ) (lower : 1 < slope)
    (upper : slope < 3) (digit : Fin 4) :
    (exclusiveInterval slope digit).Nonempty := by
  apply Set.nonempty_Icc.mpr
  fin_cases digit <;>
    norm_num [exclusiveInterval, lowerCoefficient, upperCoefficient] <;> linarith

theorem exclusiveInterval_infDist_bounds (slope tail : ℝ) (lower : 1 < slope)
    (upper : slope < 3) (digit : Fin 4) :
    ((lowerCoefficient digit.val).1 * slope + (lowerCoefficient digit.val).2) / 6 -
      Metric.infDist tail (exclusiveInterval slope digit) ≤ tail ∧
    tail ≤ ((upperCoefficient digit.val).1 * slope + (upperCoefficient digit.val).2) / 6 +
      Metric.infDist tail (exclusiveInterval slope digit) := by
  obtain ⟨nearest, membership, distance⟩ := isCompact_Icc.exists_infDist_eq_dist
    (exclusiveInterval_nonempty slope lower upper digit) tail
  have absolute : |tail - nearest| ≤ Metric.infDist tail (exclusiveInterval slope digit) := by
    unfold exclusiveInterval
    rw [distance, Real.dist_eq]
  have bounds := abs_le.mp absolute
  change _ ≤ nearest ∧ nearest ≤ _ at membership
  constructor <;> linarith [membership.1, membership.2, bounds.1, bounds.2]

/-- The distance-to-exclusive-domain formulation used in the frozen article. -/
theorem infDist_exclusive_domains_eventually_periodic
    (slope : ℝ) (slope_lower : 11 / 9 < slope) (slope_upper : slope < 2027 / 1624)
    (digits : ℕ → Fin 4) (tails : ℕ → ℝ)
    (vanishing : ∀ ε > 0, ∃ start, ∀ n ≥ start,
      Metric.infDist (tails n) (exclusiveInterval slope (digits n)) < ε)
    (recurrence : ∀ n, tails (n+1) = 3 * tails n -
      (((digits n).val / 2 : ℕ) : ℝ) * slope - (((digits n).val % 2 : ℕ) : ℝ)) :
    ∃ start, ∀ n ≥ start, digits (n+4) = digits n := by
  apply exclusive_domains_eventually_periodic slope slope_lower slope_upper digits tails
    (fun n => Metric.infDist (tails n) (exclusiveInterval slope (digits n)))
    (fun _ => Metric.infDist_nonneg) vanishing recurrence
  · intro n
    exact (exclusiveInterval_infDist_bounds slope (tails n) (by linarith) (by linarith)
      (digits n)).1
  · intro n
    exact (exclusiveInterval_infDist_bounds slope (tails n) (by linarith) (by linarith)
      (digits n)).2

end LambdaCantor.Classical
