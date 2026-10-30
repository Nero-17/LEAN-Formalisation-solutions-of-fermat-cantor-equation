import LambdaCantor.ClassicalBridge
import LambdaCantor.External.Positional

noncomputable section
namespace LambdaCantor.Classical

theorem rational_address_of_eventually_periodic (digits : ℕ → Bool)
    (periodic : ∃ start period : ℕ, 0 < period ∧
      ∀ j ≥ start, digits (j+period) = digits j) :
    ∃ rational : ℚ, (rational : ℝ) = address (1/3) digits := by
  rw [address_third_eq_ofDigits]
  apply External.rational_of_eventually_periodic_digits (by norm_num)
  obtain ⟨start, period, positive, repeats⟩ := periodic
  exact ⟨start, period, positive, fun j hj => congrArg (fun bit =>
    cond bit (2 : Fin 3) 0) (repeats j hj)⟩

theorem rational_affine_cylinder (offset : ℕ) (depth : ℕ) (value : ℝ)
    (rational_value : ∃ rational : ℚ, (rational : ℝ) = value) :
    ∃ rational : ℚ, (rational : ℝ) = (offset + value) / 3 ^ depth := by
  obtain ⟨rational, represents⟩ := rational_value
  refine ⟨(offset + rational) / 3 ^ depth, ?_⟩
  push_cast
  rw [represents]

end LambdaCantor.Classical
