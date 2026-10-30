import LambdaCantor.AE.CenteredResidual

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.AE

theorem centered_variable_power_tendsto_zero {lower upper : ℝ}
    (hlower : 0 < lower) (hinterval : lower ≤ upper) (hless : upper < 1)
    (ratios : ℕ → ℝ) (hratios : ∀ index, ratios index ∈ Set.Icc lower upper) :
    Tendsto (fun index => (ratios index) ^ index) atTop (𝓝 0) :=
  squeeze_zero (fun index => pow_nonneg (hlower.le.trans (hratios index).1) _)
    (fun index => pow_le_pow_left₀ (hlower.le.trans (hratios index).1) (hratios index).2 _)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (hlower.le.trans hinterval) hless)

theorem centered_variable_power_derivative_tendsto_zero {lower upper : ℝ}
    (hlower : 0 < lower) (hinterval : lower ≤ upper) (hless : upper < 1)
    (ratios : ℕ → ℝ) (hratios : ∀ index, ratios index ∈ Set.Icc lower upper) :
    Tendsto (fun index : ℕ => (index : ℝ) * (ratios index) ^ (index - 1)) atTop (𝓝 0) := by
  have hnorm : ‖upper‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hlower.le.trans hinterval)]
  have hdecay : Tendsto (fun index : ℕ => (index : ℝ) * upper ^ index / lower) atTop (𝓝 0) := by
    simpa only [pow_one, zero_div] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).tendsto_atTop_zero.div_const lower
  apply squeeze_zero' (Eventually.of_forall (fun index =>
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hlower.le.trans (hratios index).1) _)))
  · filter_upwards [eventually_ge_atTop 1] with index hindex
    have hpower := centered_shifted_power_bound hlower (hratios index).1 (hratios index).2 index 1 hindex
    simpa only [pow_one, mul_div_assoc] using
      mul_le_mul_of_nonneg_left hpower (Nat.cast_nonneg index)
  · simpa only [mul_div_assoc] using hdecay

theorem centeredHorizontalFactor_bounds (tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1) :
    |centeredHorizontalFactor tailDepth digits ratio - 1| ≤ ratio ^ tailDepth := by
  have haddress := cantorSet_subset_unitInterval hpositive.le hless
    (show address ratio digits ∈ cantorSet ratio from ⟨digits, rfl⟩)
  have hpower := pow_nonneg hpositive.le tailDepth
  unfold centeredHorizontalFactor
  apply abs_le.mpr
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left haddress.2 hpower,
    mul_nonneg hpower haddress.1]

theorem centeredTailFactor_bounds (tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1) :
    |centeredTailFactor tailDepth digits ratio - 1| ≤ ratio ^ tailDepth := by
  have haddress := cantorSet_subset_unitInterval hpositive.le hless
    (show address ratio digits ∈ cantorSet ratio from ⟨digits, rfl⟩)
  unfold centeredTailFactor
  have hproduct := mul_nonneg (pow_nonneg hpositive.le tailDepth) haddress.1
  have hbound := mul_le_mul_of_nonneg_left haddress.2 (pow_nonneg hpositive.le tailDepth)
  apply abs_le.mpr
  constructor <;> nlinarith

theorem centered_factors_tendsto_one {lower upper : ℝ}
    (hlower : 0 < lower) (hinterval : lower ≤ upper) (hless : upper < 1)
    (ratios : ℕ → ℝ) (hratios : ∀ index, ratios index ∈ Set.Icc lower upper)
    (digits : ℕ → ℕ → Bool) :
    Tendsto (fun index => centeredHorizontalFactor index (digits index) (ratios index)) atTop (𝓝 1) ∧
      Tendsto (fun index => centeredTailFactor index (digits index) (ratios index)) atTop (𝓝 1) := by
  have hpower := centered_variable_power_tendsto_zero hlower hinterval hless ratios hratios
  constructor
  · apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq]
    exact squeeze_zero (fun _ => abs_nonneg _) (fun index =>
      centeredHorizontalFactor_bounds index (digits index) (hlower.trans_le (hratios index).1)
        ((hratios index).2.trans_lt hless)) hpower
  · apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq]
    exact squeeze_zero (fun _ => abs_nonneg _) (fun index =>
      centeredTailFactor_bounds index (digits index) (hlower.trans_le (hratios index).1)
        ((hratios index).2.trans_lt hless)) hpower

theorem centered_factor_derivative_bounds (tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio bound : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1)
    (hbound : |deriv (fun parameter => address parameter digits) ratio| ≤ bound) :
    |deriv (centeredHorizontalFactor tailDepth digits) ratio| ≤
        2 * (tailDepth : ℝ) * ratio ^ (tailDepth - 1) + ratio ^ tailDepth * bound ∧
      |deriv (centeredTailFactor tailDepth digits) ratio| ≤
        (tailDepth : ℝ) * ratio ^ (tailDepth - 1) + ratio ^ tailDepth * bound := by
  have haddress := cantorSet_subset_unitInterval hpositive.le hless
    (show address ratio digits ∈ cantorSet ratio from ⟨digits, rfl⟩)
  have haddressNonnegative := haddress.1
  have hmiddle : |(tailDepth : ℝ) * ratio ^ (tailDepth - 1) * address ratio digits| ≤
      (tailDepth : ℝ) * ratio ^ (tailDepth - 1) := by
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) haddress.2
  have hlast : |ratio ^ tailDepth * deriv (fun parameter => address parameter digits) ratio| ≤
      ratio ^ tailDepth * bound := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hpositive.le _)]
    exact mul_le_mul_of_nonneg_left hbound (pow_nonneg hpositive.le _)
  constructor
  · rw [(centeredHorizontalFactor_hasDerivAt tailDepth digits hpositive hless).deriv]
    have htriangle := (abs_add_le
      (-(tailDepth : ℝ) * ratio ^ (tailDepth - 1) +
        (tailDepth : ℝ) * ratio ^ (tailDepth - 1) * address ratio digits)
      (ratio ^ tailDepth * deriv (fun parameter => address parameter digits) ratio)).trans
      (add_le_add (abs_add_le (-(tailDepth : ℝ) * ratio ^ (tailDepth - 1))
        ((tailDepth : ℝ) * ratio ^ (tailDepth - 1) * address ratio digits)) (le_refl _))
    have hnegative : |-(tailDepth : ℝ) * ratio ^ (tailDepth - 1)| =
        (tailDepth : ℝ) * ratio ^ (tailDepth - 1) := by
      rw [neg_mul, abs_neg, abs_of_nonneg (by positivity)]
    rw [hnegative] at htriangle
    linarith
  · rw [(centeredTailFactor_hasDerivAt tailDepth digits hpositive hless).deriv, abs_neg]
    exact (abs_add_le _ _).trans (add_le_add hmiddle hlast)

theorem centered_factor_derivatives_tendsto_zero {lower upper : ℝ}
    (hlower : 0 < lower) (hinterval : lower ≤ upper) (hless : upper < 1)
    (ratios : ℕ → ℝ) (hratios : ∀ index, ratios index ∈ Set.Icc lower upper)
    (digits : ℕ → ℕ → Bool) :
    Tendsto (fun index => deriv (centeredHorizontalFactor index (digits index)) (ratios index)) atTop (𝓝 0) ∧
      Tendsto (fun index => deriv (centeredTailFactor index (digits index)) (ratios index)) atTop (𝓝 0) := by
  have hpower := centered_variable_power_tendsto_zero hlower hinterval hless ratios hratios
  have hpowerDerivative := centered_variable_power_derivative_tendsto_zero hlower hinterval hless ratios hratios
  have hbounds := fun index => centered_factor_derivative_bounds index (digits index)
    (hlower.trans_le (hratios index).1) ((hratios index).2.trans_lt hless)
    (show |deriv (fun parameter => address parameter (digits index)) (ratios index)| ≤
      addressParameterDerivativeBound upper from by
      rw [(hasDerivAt_address_parameter (hlower.trans_le (hratios index).1)
        ((hratios index).2.trans_lt hless) (digits index)).deriv]
      exact address_parameter_derivative_bound (hlower.le.trans (hratios index).1)
        (hratios index).2 hless (digits index))
  constructor
  · apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq, sub_zero]
    apply squeeze_zero (fun _ => abs_nonneg _) (fun index => (hbounds index).1)
    simpa only [zero_mul, mul_zero, zero_add, mul_assoc] using
      (hpowerDerivative.const_mul 2).add (hpower.mul_const (addressParameterDerivativeBound upper))
  · apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq, sub_zero]
    apply squeeze_zero (fun _ => abs_nonneg _) (fun index => (hbounds index).2)
    simpa only [zero_mul, zero_add] using
      hpowerDerivative.add (hpower.mul_const (addressParameterDerivativeBound upper))

end LambdaCantor.AE
