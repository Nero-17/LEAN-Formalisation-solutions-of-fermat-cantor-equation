import LambdaCantor.Circle.ResidualSlope
import LambdaCantor.Circle.RootExistence
import LambdaCantor.Circle.AddressDerivative

noncomputable section
namespace LambdaCantor.Circle

def expandedCircleResidual (depth : ℕ) (firstTail secondTail : ℝ → ℝ) (ratio : ℝ) : ℝ :=
  -(4 * ratio - 1 - ratio ^ 2) +
    2 * ratio ^ (2 * depth + 1) * ((1 - ratio) * firstTail ratio + secondTail ratio) +
    ratio ^ (4 * depth + 2) * (firstTail ratio) ^ 2 +
    ratio ^ (2 * depth + 2) * (1 - ratio ^ (2 * depth) * secondTail ratio) ^ 2

theorem expandedCircleResidual_eq (depth : ℕ) (firstTail secondTail : ℝ → ℝ) (ratio : ℝ) :
    expandedCircleResidual depth firstTail secondTail ratio = circleRootResidual depth firstTail secondTail ratio := by
  have twice : ratio ^ (2 * depth) = (ratio ^ depth) ^ 2 := by rw [Nat.mul_comm, pow_mul]
  have four : ratio ^ (4 * depth) = (ratio ^ depth) ^ 4 := by rw [Nat.mul_comm, pow_mul]
  unfold expandedCircleResidual circleRootResidual
  rw [pow_add, pow_add, pow_add, twice, four]
  ring

theorem hasDerivAt_circleResidual (depth : ℕ) (ratio : ℝ) (firstTail secondTail : ℝ → ℝ)
    (firstDerivative secondDerivative : ℝ)
    (first_differentiable : HasDerivAt firstTail firstDerivative ratio)
    (second_differentiable : HasDerivAt secondTail secondDerivative ratio) :
    HasDerivAt (expandedCircleResidual depth firstTail secondTail)
      (circleResidualSlope depth ratio (firstTail ratio) (secondTail ratio) firstDerivative secondDerivative) ratio := by
  have main := (((hasDerivAt_id ratio).const_mul 4).sub_const 1).sub ((hasDerivAt_id ratio).pow 2)
  have first_factor := (((hasDerivAt_id ratio).const_sub 1).mul first_differentiable).add second_differentiable
  have first_term := (((hasDerivAt_id ratio).pow (2 * depth + 1)).const_mul 2).mul first_factor
  have second_term := ((hasDerivAt_id ratio).pow (4 * depth + 2)).mul (first_differentiable.pow 2)
  have last_factor := ((((hasDerivAt_id ratio).pow (2 * depth)).mul second_differentiable).const_sub 1)
  have third_term := ((hasDerivAt_id ratio).pow (2 * depth + 2)).mul (last_factor.pow 2)
  have second_index : 4 * depth + 2 - 1 = 4 * depth + 1 := by omega
  have third_index : 2 * depth + 2 - 1 = 2 * depth + 1 := by omega
  convert! ((main.neg.add first_term).add second_term).add third_term using 1
  all_goals
    first
    | rfl
    | funext parameter
      simp only [expandedCircleResidual,Pi.neg_apply,Pi.add_apply,Pi.sub_apply,
        Pi.mul_apply,Pi.pow_apply,id_eq]
    | unfold circleResidualSlope
      simp only [Pi.neg_apply,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,id_eq,
        second_index,third_index,Nat.add_sub_cancel,Nat.add_sub_cancel_right,Nat.reduceSub,
        Nat.cast_ofNat,pow_one,mul_one]
      ring

/-- Actual address residuals have a uniform strictly negative derivative. -/
theorem circle_address_residual_transverse (depth : ℕ) (large : 2 ≤ depth)
    (ratio : ℝ) (positive : 0 < ratio) (upper : ratio ≤ (7 / 25 : ℝ))
    (firstDigits secondDigits : ℕ → Bool) :
    ∃ derivative : ℝ,
      HasDerivAt (expandedCircleResidual depth (fun parameter => address parameter firstDigits)
        (fun parameter => address parameter secondDigits)) derivative ratio ∧ derivative < -2 := by
  have less_one : ratio < 1 := by linarith
  have first_bounds := cantorSet_subset_unitInterval positive.le less_one (Set.mem_range_self firstDigits)
  have second_bounds := cantorSet_subset_unitInterval positive.le less_one (Set.mem_range_self secondDigits)
  refine ⟨circleResidualSlope depth ratio (address ratio firstDigits) (address ratio secondDigits)
    (addressParameterDerivative ratio firstDigits) (addressParameterDerivative ratio secondDigits), ?_, ?_⟩
  · exact hasDerivAt_circleResidual depth ratio _ _ _ _
      (hasDerivAt_address_parameter positive less_one firstDigits)
      (hasDerivAt_address_parameter positive less_one secondDigits)
  · exact (circle_residual_slope_bounds depth large ratio _ _ _ _ positive.le upper
      first_bounds.1 first_bounds.2 second_bounds.1 second_bounds.2
      (address_derivative_le_three positive.le upper firstDigits)
      (address_derivative_le_three positive.le upper secondDigits)).2

end LambdaCantor.Circle

