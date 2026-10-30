import LambdaCantor.Circle.Transversality
import LambdaCantor.Circle.AddressRoots
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
namespace LambdaCantor.Circle

theorem circle_address_residual_strictAnti (depth : ℕ) (large : 2 ≤ depth)
    (firstDigits secondDigits : ℕ → Bool) :
    StrictAntiOn (expandedCircleResidual depth (fun ratio => address ratio firstDigits)
      (fun ratio => address ratio secondDigits)) (Set.Icc onset (7 / 25 : ℝ)) := by
  have differentiability (ratio : ℝ) (member : ratio ∈ Set.Icc onset (7 / 25 : ℝ)) :=
    circle_address_residual_transverse depth large ratio (lt_of_lt_of_le onset_pos member.1)
      member.2 firstDigits secondDigits
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · intro ratio member
    obtain ⟨derivative, differentiable, negative⟩ := differentiability ratio member
    exact differentiable.continuousAt.continuousWithinAt
  · intro ratio member
    have closed_member : ratio ∈ Set.Icc onset (7 / 25 : ℝ) := interior_subset member
    obtain ⟨derivative, differentiable, negative⟩ := differentiability ratio closed_member
    rw [differentiable.deriv]
    linarith

/-- Every address pair has exactly one root; existence, exact coding and
uniform transversality all precede this consequence. -/
theorem circle_address_root_exists_unique (depth : ℕ) (large : 2 ≤ depth)
    (firstDigits secondDigits : ℕ → Bool) :
    ∃! ratio : ℝ, ratio ∈ Set.Ioo onset (7 / 25 : ℝ) ∧
      expandedCircleResidual depth (fun parameter => address parameter firstDigits)
        (fun parameter => address parameter secondDigits) ratio = 0 := by
  obtain ⟨ratio, member, x, x_mem, y, y_mem, x_eq, y_eq, equation⟩ :=
    circle_root_exists_for_addresses depth large firstDigits secondDigits
  have identity := root_residual_identity ratio (ratio ^ depth)
    (address ratio firstDigits) (address ratio secondDigits)
  rw [x_eq, y_eq] at equation
  have residual_zero : circleRootResidual depth (fun parameter => address parameter firstDigits)
      (fun parameter => address parameter secondDigits) ratio = 0 := by
    have product_zero : (ratio ^ depth) ^ 2 *
        circleRootResidual depth (fun parameter => address parameter firstDigits)
          (fun parameter => address parameter secondDigits) ratio = 0 := by
      unfold circleRootResidual
      linarith
    exact (mul_eq_zero.mp product_zero).resolve_left (ne_of_gt (pow_pos (pow_pos (lt_trans onset_pos member.1) _) _))
  have expanded_zero : expandedCircleResidual depth (fun parameter => address parameter firstDigits)
      (fun parameter => address parameter secondDigits) ratio = 0 := by
    rw [expandedCircleResidual_eq]
    exact residual_zero
  refine ⟨ratio, ⟨member, expanded_zero⟩, ?_⟩
  intro other other_root
  have antitone := circle_address_residual_strictAnti depth large firstDigits secondDigits
  apply antitone.injOn ⟨other_root.1.1.le, other_root.1.2.le⟩ ⟨member.1.le, member.2.le⟩
  rw [other_root.2, expanded_zero]

end LambdaCantor.Circle
