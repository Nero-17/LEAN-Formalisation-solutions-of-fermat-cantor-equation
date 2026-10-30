import LambdaCantor.Integer.AffineImage
import LambdaCantor.Classical.Cylinders
import LambdaCantor.Addresses
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.NumberTheory.Real.Irrational

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.RealPowers
open Integer

/-- Exact outer-third quotient interval at the critical contraction. This uses
the established affine Cantor image, including the endpoint q=2/3. -/
theorem outer_third_quotient_realization (quotient : ℝ)
    (bounds : quotient ∈ Set.Icc (2/3 : ℝ) (3/2)) :
    ∃ numerator ∈ _root_.cantorSet, ∃ denominator ∈ _root_.cantorSet,
      (2+numerator)/(2+denominator) = quotient := by
  have quotient_positive : 0 < quotient := by linarith [bounds.1]
  have reflected : ∀ coordinate ∈ _root_.cantorSet,
      1-coordinate ∈ _root_.cantorSet := by
    intro coordinate membership
    rw [← cantorSet_third_eq] at membership ⊢
    exact one_sub_mem_cantorSet (by norm_num) (by norm_num) membership
  by_cases above_one : 1 ≤ quotient
  · obtain ⟨first, first_mem, second, second_mem, equation⟩ :=
      affine_fibre_nonempty quotient ((3*quotient-2)/2) above_one
        (by linarith [bounds.2]) ⟨by linarith, by linarith [bounds.2]⟩
    have first_bounds := _root_.cantorSet_subset_unitInterval first_mem
    refine ⟨second, second_mem, 1-first, reflected first first_mem, ?_⟩
    apply (div_eq_iff (by linarith [first_bounds.2] : 2+(1-first) ≠ 0)).mpr
    nlinarith [equation]
  · have inverse_lower : 1 ≤ 1/quotient :=
      (le_div_iff₀ quotient_positive).mpr (by linarith)
    have inverse_upper : 1/quotient ≤ 3 :=
      (div_le_iff₀ quotient_positive).mpr (by linarith [bounds.1])
    have level_lower : 0 ≤ (3*quotient-2)/(2*quotient) :=
      div_nonneg (by linarith [bounds.1]) (by positivity)
    have level_upper : (3*quotient-2)/(2*quotient) ≤ ((1/quotient)+1)/2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2*quotient)).mpr
      have inverse_cancel : (1/quotient)*quotient = 1 := one_div_mul_cancel quotient_positive.ne'
      nlinarith
    obtain ⟨first, first_mem, second, second_mem, equation⟩ :=
      affine_fibre_nonempty (1/quotient) ((3*quotient-2)/(2*quotient))
        inverse_lower inverse_upper ⟨level_lower, level_upper⟩
    have second_bounds := _root_.cantorSet_subset_unitInterval second_mem
    refine ⟨first, first_mem, 1-second, reflected second second_mem, ?_⟩
    apply (div_eq_iff (by linarith [second_bounds.2] : 2+(1-second) ≠ 0)).mpr
    have cleared := congrArg (fun value : ℝ => 2*quotient*value) equation
    field_simp [quotient_positive.ne'] at cleared
    nlinarith [cleared]

theorem prefixValue_tendsto_address (digits : ℕ → Bool) :
    Tendsto (prefixValue (1/3) digits) atTop (𝓝 (address (1/3) digits)) := by
  have partial_sums := (address_summable (by norm_num : (0 : ℝ) ≤ 1/3)
    (by norm_num) digits).hasSum.tendsto_sum_nat
  change Tendsto (fun depth => (1-(1/3 : ℝ))*
    ∑ j ∈ Finset.range depth, (if digits j then (1 : ℝ) else 0)*(1/3 : ℝ)^j)
    atTop (𝓝 ((1-(1/3 : ℝ))*
      ∑' j : ℕ, (if digits j then (1 : ℝ) else 0)*(1/3 : ℝ)^j))
  exact tendsto_const_nhds.mul partial_sums

def finiteOuterEndpoint (digits : ℕ → Bool) (depth : ℕ) : ℝ :=
  (2+prefixValue (1/3) digits depth)/3

theorem finiteOuterEndpoint_bounds (digits : ℕ → Bool) (depth : ℕ) :
    0 < finiteOuterEndpoint digits depth ∧ finiteOuterEndpoint digits depth < 1 := by
  have bounds := Classical.prefix_square_bounds digits depth
  have side_positive : 0 < (1/3 : ℝ)^depth := by positivity
  unfold finiteOuterEndpoint
  constructor <;> linarith [bounds.1, bounds.2]

/-- Positive finite ternary endpoints realize quotients densely throughout
the full outer quotient interval. Their two depths may be chosen equal. -/
theorem finite_outer_quotient_in_open_interval (quotient lower upper : ℝ)
    (quotient_bounds : quotient ∈ Set.Icc (2/3 : ℝ) (3/2))
    (above : lower < quotient) (below : quotient < upper) :
    ∃ first second : ℕ → Bool, ∃ depth : ℕ,
      lower < finiteOuterEndpoint first depth/finiteOuterEndpoint second depth ∧
      finiteOuterEndpoint first depth/finiteOuterEndpoint second depth < upper := by
  obtain ⟨numerator, numerator_mem, denominator, denominator_mem, equation⟩ :=
    outer_third_quotient_realization quotient quotient_bounds
  rw [← cantorSet_third_eq] at numerator_mem denominator_mem
  obtain ⟨first, first_eq⟩ := numerator_mem
  obtain ⟨second, second_eq⟩ := denominator_mem
  have first_limit : Tendsto (fun depth => (2+prefixValue (1/3) first depth)/3)
      atTop (𝓝 ((2+address (1/3) first)/3)) :=
    (tendsto_const_nhds.add (prefixValue_tendsto_address first)).div_const 3
  have second_limit : Tendsto (fun depth => (2+prefixValue (1/3) second depth)/3)
      atTop (𝓝 ((2+address (1/3) second)/3)) :=
    (tendsto_const_nhds.add (prefixValue_tendsto_address second)).div_const 3
  have denominator_bounds := address_nonnegative (by norm_num : (0 : ℝ) ≤ 1/3) (by norm_num) second
  have denominator_nonzero : (2+address (1/3) second)/3 ≠ 0 := by positivity
  have quotient_limit := first_limit.div second_limit denominator_nonzero
  have limit_value : ((2+address (1/3) first)/3)/((2+address (1/3) second)/3) = quotient := by
    rw [first_eq, second_eq]
    simpa only [div_div_div_cancel_right₀ (by norm_num : (3 : ℝ) ≠ 0)] using equation
  rw [limit_value] at quotient_limit
  obtain ⟨depth, member⟩ := (quotient_limit.eventually (isOpen_Ioo.mem_nhds ⟨above, below⟩)).exists
  exact ⟨first, second, depth, member⟩

/-- The elementary two-orientation normalization used by the manuscript.
A finite endpoint quotient puts every coefficient in [1,3] into the stated
small good band or its reciprocal. The two branches retain their scale
factor explicitly. -/
theorem finite_endpoint_normalized_slope (normalized : ℝ)
    (lower : 1 ≤ normalized) (upper : normalized ≤ 3) :
    ∃ first second : ℕ → Bool, ∃ depth : ℕ,
      (11/9 < normalized*(finiteOuterEndpoint first depth/finiteOuterEndpoint second depth) ∧
        normalized*(finiteOuterEndpoint first depth/finiteOuterEndpoint second depth) < 2027/1624) ∨
      (1624/2027 < (normalized/3)*(finiteOuterEndpoint first depth/finiteOuterEndpoint second depth) ∧
        (normalized/3)*(finiteOuterEndpoint first depth/finiteOuterEndpoint second depth) < 9/11) := by
  have positive : 0 < normalized := by linarith
  by_cases first_range : normalized ≤ 9/5
  · have quotient_bounds : (123/100)/normalized ∈ Set.Icc (2/3 : ℝ) (3/2) := by
      constructor
      · apply (le_div_iff₀ positive).mpr
        linarith
      · apply (div_le_iff₀ positive).mpr
        linarith
    obtain ⟨first, second, depth, first_lower, first_upper⟩ :=
      finite_outer_quotient_in_open_interval ((123/100)/normalized)
        ((11/9)/normalized) ((2027/1624)/normalized) quotient_bounds
        ((div_lt_div_iff_of_pos_right positive).mpr (by norm_num))
        ((div_lt_div_iff_of_pos_right positive).mpr (by norm_num))
    refine ⟨first, second, depth, Or.inl ⟨?_, ?_⟩⟩
    · have cleared := (div_lt_iff₀ positive).mp first_lower
      nlinarith
    · have cleared := (lt_div_iff₀ positive).mp first_upper
      nlinarith
  · have scaled_positive : 0 < normalized/3 := by positivity
    have quotient_bounds : (100/123)/(normalized/3) ∈ Set.Icc (2/3 : ℝ) (3/2) := by
      constructor
      · apply (le_div_iff₀ scaled_positive).mpr
        linarith
      · apply (div_le_iff₀ scaled_positive).mpr
        linarith
    obtain ⟨first, second, depth, first_lower, first_upper⟩ :=
      finite_outer_quotient_in_open_interval ((100/123)/(normalized/3))
        ((1624/2027)/(normalized/3)) ((9/11)/(normalized/3)) quotient_bounds
        ((div_lt_div_iff_of_pos_right scaled_positive).mpr (by norm_num))
        ((div_lt_div_iff_of_pos_right scaled_positive).mpr (by norm_num))
    refine ⟨first, second, depth, Or.inr ⟨?_, ?_⟩⟩
    · have cleared := (div_lt_iff₀ scaled_positive).mp first_lower
      nlinarith
    · have cleared := (lt_div_iff₀ scaled_positive).mp first_upper
      nlinarith

theorem finiteOuterEndpoint_rational (digits : ℕ → Bool) (depth : ℕ) :
    ∃ rational : ℚ, (rational : ℝ) = finiteOuterEndpoint digits depth := by
  refine ⟨(2+(1-(1/3 : ℚ))*
    ∑ j ∈ Finset.range depth, (if digits j then (1 : ℚ) else 0)*(1/3 : ℚ)^j)/3, ?_⟩
  unfold finiteOuterEndpoint prefixValue
  push_cast <;> simp only [apply_ite, Rat.cast_one, Rat.cast_zero]

/-- A source slope obtained from an irrational exponent by these finite
endpoint quotients and an integral ternary shift remains irrational. -/
theorem finite_endpoint_slope_irrational {exponent : ℝ}
    (irrational : Irrational exponent) (first second : ℕ → Bool) (depth : ℕ) (shift : ℤ) :
    Irrational (exponent*(finiteOuterEndpoint first depth/finiteOuterEndpoint second depth)*
      (3 : ℝ)^shift) := by
  obtain ⟨numerator, numerator_eq⟩ := finiteOuterEndpoint_rational first depth
  obtain ⟨denominator, denominator_eq⟩ := finiteOuterEndpoint_rational second depth
  have numerator_nonzero : numerator ≠ 0 := by
    intro zero
    have positive := (finiteOuterEndpoint_bounds first depth).1
    rw [← numerator_eq, zero, Rat.cast_zero] at positive
    exact lt_irrefl 0 positive
  have denominator_nonzero : denominator ≠ 0 := by
    intro zero
    have positive := (finiteOuterEndpoint_bounds second depth).1
    rw [← denominator_eq, zero, Rat.cast_zero] at positive
    exact lt_irrefl 0 positive
  have factor_nonzero : (numerator/denominator*(3 : ℚ)^shift) ≠ 0 := by
    exact mul_ne_zero (div_ne_zero numerator_nonzero denominator_nonzero) (zpow_ne_zero _ (by norm_num))
  have result := irrational.mul_ratCast factor_nonzero
  convert result using 1
  push_cast
  rw [numerator_eq, denominator_eq]
  ring

end LambdaCantor.RealPowers

