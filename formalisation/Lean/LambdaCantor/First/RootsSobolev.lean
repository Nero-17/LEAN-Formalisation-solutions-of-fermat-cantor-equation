import LambdaCantor.First.RootsFourierCoupling

noncomputable section
open MeasureTheory

namespace LambdaCantor.First.Roots

/-- Convolving with an absolutely continuous factor preserves absolute
continuity, including when the other factor is singular. -/
theorem convolution_absolutelyContinuous (left right : Measure ℝ)
    [IsFiniteMeasure left] [IsFiniteMeasure right]
    (left_absolutelyContinuous : left ≪ volume) : left ∗ right ≪ volume := by
  rw [Measure.conv_comm]
  exact Measure.conv_absolutelyContinuous left_absolutelyContinuous

/-- Power Fourier decay absorbs a positive Sobolev weight. The unit bound is
the characteristic-function bound for a probability measure; decay is only
needed outside the unit interval, so no convention at zero is involved. -/
theorem fourier_decay_weight_bound (value : ℂ) (frequency order constant : ℝ)
    (order_pos : 0 < order) (constant_nonnegative : 0 ≤ constant)
    (unit_bound : ‖value‖ ≤ 1)
    (decay : 1 < |frequency| → ‖value‖ ≤ constant * |frequency| ^ (-order)) :
    (1 + frequency ^ 2) ^ order * ‖value‖ ^ 2 ≤
      (2 : ℝ) ^ order * (1 + constant ^ 2) := by
  have two_power_pos : 0 < (2 : ℝ) ^ order := Real.rpow_pos_of_pos (by norm_num) _
  by_cases high : 1 < |frequency|
  · have absolute_pos : 0 < |frequency| := lt_trans zero_lt_one high
    have frequency_square_ge : 1 ≤ frequency ^ 2 := by
      have square := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg frequency)).2 high.le
      simpa only [one_pow, sq_abs] using square
    have weight_bound : (1 + frequency ^ 2) ^ order ≤
        (2 : ℝ) ^ order * |frequency| ^ (2 * order) := by
      calc
        _ ≤ (2 * frequency ^ 2) ^ order :=
          Real.rpow_le_rpow (by positivity) (by linarith) order_pos.le
        _ = _ := by
          rw [Real.mul_rpow (by norm_num) (sq_nonneg _), ← sq_abs,
            ← Real.rpow_two |frequency|, ← Real.rpow_mul absolute_pos.le]
    have square_bound : ‖value‖ ^ 2 ≤ constant ^ 2 * (|frequency| ^ (-order)) ^ 2 := by
      have inequality := (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg constant_nonnegative (Real.rpow_nonneg absolute_pos.le _))).2 (decay high)
      simpa only [mul_pow] using inequality
    have cancellation : |frequency| ^ (2 * order) * (|frequency| ^ (-order)) ^ 2 = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul absolute_pos.le,
        ← Real.rpow_add absolute_pos]
      convert Real.rpow_zero |frequency| using 1 <;> ring
    calc
      _ ≤ ((2 : ℝ) ^ order * |frequency| ^ (2 * order)) *
          (constant ^ 2 * (|frequency| ^ (-order)) ^ 2) :=
        mul_le_mul weight_bound square_bound (sq_nonneg _) (by positivity)
      _ = (2 : ℝ) ^ order * constant ^ 2 := by
        calc
          _ = (2 : ℝ) ^ order * constant ^ 2 *
              (|frequency| ^ (2 * order) * (|frequency| ^ (-order)) ^ 2) := by ring
          _ = _ := by rw [cancellation, mul_one]
      _ ≤ _ := by nlinarith
  · have frequency_square_le : frequency ^ 2 ≤ 1 := by
      have square := (sq_le_sq₀ (abs_nonneg frequency) (by norm_num : (0 : ℝ) ≤ 1)).2
        (le_of_not_gt high)
      simpa only [one_pow, sq_abs] using square
    have weight_bound := Real.rpow_le_rpow (show 0 ≤ 1 + frequency ^ 2 by positivity)
      (show 1 + frequency ^ 2 ≤ 2 by linarith) order_pos.le
    have square_bound := (sq_le_sq₀ (norm_nonneg value) (by norm_num : (0 : ℝ) ≤ 1)).2 unit_bound
    have product_bound := mul_le_mul weight_bound square_bound (sq_nonneg ‖value‖) two_power_pos.le
    nlinarith [sq_nonneg constant]

/-- The actual convolution characteristic function gains a positive weighted
L2 estimate from one L2 Fourier factor and one power-decaying factor. -/
theorem convolution_weighted_fourier_energy (left right : Measure ℝ)
    [IsProbabilityMeasure left] [IsProbabilityMeasure right]
    (order constant : ℝ) (order_pos : 0 < order) (constant_nonnegative : 0 ≤ constant)
    (left_energy_integrable : Integrable (fun frequency : ℝ => ‖charFun left frequency‖ ^ 2))
    (right_decay : ∀ frequency : ℝ, 1 < |frequency| →
      ‖charFun right frequency‖ ≤ constant * |frequency| ^ (-order)) :
    Integrable (fun frequency : ℝ =>
      (1 + frequency ^ 2) ^ order * ‖charFun (left ∗ right) frequency‖ ^ 2) ∧
    (∫ frequency : ℝ,
      (1 + frequency ^ 2) ^ order * ‖charFun (left ∗ right) frequency‖ ^ 2) ≤
        (2 : ℝ) ^ order * (1 + constant ^ 2) *
          ∫ frequency : ℝ, ‖charFun left frequency‖ ^ 2 := by
  have pointwise (frequency : ℝ) :
      (1 + frequency ^ 2) ^ order * ‖charFun (left ∗ right) frequency‖ ^ 2 ≤
        ((2 : ℝ) ^ order * (1 + constant ^ 2)) * ‖charFun left frequency‖ ^ 2 := by
    have decay_bound := fourier_decay_weight_bound (charFun right frequency) frequency order constant
      order_pos constant_nonnegative (by simpa using norm_charFun_le (μ := right) frequency)
      (right_decay frequency)
    have product_bound := mul_le_mul_of_nonneg_right decay_bound
      (sq_nonneg ‖charFun left frequency‖)
    rw [charFun_conv, norm_mul, mul_pow]
    nlinarith
  have majorant_integrable := left_energy_integrable.const_mul
    ((2 : ℝ) ^ order * (1 + constant ^ 2))
  have convolution_integrable : Integrable (fun frequency : ℝ =>
      (1 + frequency ^ 2) ^ order * ‖charFun (left ∗ right) frequency‖ ^ 2) := by
    apply majorant_integrable.mono'
    · have weight_continuous : Continuous (fun frequency : ℝ => (1 + frequency ^ 2) ^ order) := by
        apply Continuous.rpow_const
        · fun_prop
        · intro frequency
          left
          positivity
      exact (weight_continuous.mul ((continuous_charFun (μ := left ∗ right)).norm.pow 2)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun frequency => by
        change ‖(1 + frequency ^ 2) ^ order * ‖charFun (left ∗ right) frequency‖ ^ 2‖ ≤
          ((2 : ℝ) ^ order * (1 + constant ^ 2)) * ‖charFun left frequency‖ ^ 2
        have weighted_nonnegative :
            0 ≤ (1 + frequency ^ 2) ^ order * ‖charFun (left ∗ right) frequency‖ ^ 2 :=
          mul_nonneg (Real.rpow_nonneg (by positivity) order) (sq_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg weighted_nonnegative]
        exact pointwise frequency)
  refine ⟨convolution_integrable, ?_⟩
  calc
    _ ≤ ∫ frequency : ℝ,
        ((2 : ℝ) ^ order * (1 + constant ^ 2)) * ‖charFun left frequency‖ ^ 2 :=
      integral_mono convolution_integrable majorant_integrable pointwise
    _ = _ := integral_const_mul _ _

end LambdaCantor.First.Roots
