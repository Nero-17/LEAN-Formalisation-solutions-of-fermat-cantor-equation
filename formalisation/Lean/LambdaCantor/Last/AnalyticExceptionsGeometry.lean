import LambdaCantor.Last.AnalyticExceptionsCertificates
import LambdaCantor.Last.TwoBandSlopes

noncomputable section
namespace LambdaCantor.Last

theorem inverse_square_second_band {ratio lower upper : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hlower : 0 < lower) (horder : lower ≤ upper)
    (habove_one : upper ^ 2 < 1)
    (hband_lower : (1 - ratio) * upper ^ 2 < ratio)
    (hband_upper : 1 - ratio - ratio ^ 2 < lower ^ 2) :
    TwoBandInterval ratio (1 / upper ^ 2) (1 / lower ^ 2) := by
  have hupper : 0 < upper := hlower.trans_le horder
  have hdenominator : 0 < 1 - ratio - ratio ^ 2 := by nlinarith
  refine ⟨(lt_div_iff₀ (sq_pos_of_pos hupper)).mpr (by simpa using habove_one), ?_, Or.inr ⟨?_, ?_⟩⟩
  · exact one_div_le_one_div_of_le (sq_pos_of_pos hlower) (by nlinarith)
  · have hidentity : 1 / ratio - 1 = (1 - ratio) / ratio := by
      field_simp [hpositive.ne']
      <;> ring
    rw [hidentity, div_lt_div_iff₀ hpositive (sq_pos_of_pos hupper)]
    simpa only [mul_one, one_mul] using hband_lower
  · exact (one_div_lt_one_div (sq_pos_of_pos hlower) hdenominator).mpr hband_upper

theorem inverse_first_band {ratio lower upper : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hlower : 1 - ratio < lower) (horder : lower ≤ upper) (hupper : upper < 1)
    (hband_lower : upper * (1 - ratio - ratio ^ 2) < ratio) :
    TwoBandInterval ratio (1 / upper) (1 / lower) := by
  have hlower_positive : 0 < lower := by linarith
  have hupper_positive : 0 < upper := hlower_positive.trans_le horder
  refine ⟨(lt_div_iff₀ hupper_positive).mpr (by simpa using hupper),
    one_div_le_one_div_of_le hlower_positive horder, Or.inl ⟨?_, ?_⟩⟩
  · have hidentity : (1 / ratio - 1 - ratio) = (1 - ratio - ratio ^ 2) / ratio := by
      field_simp [hpositive.ne']
      <;> ring
    rw [hidentity, div_lt_div_iff₀ hpositive hupper_positive]
    simpa only [mul_one, one_mul, mul_comm] using hband_lower
  · exact (one_div_lt_one_div hlower_positive (by linarith)).mpr hlower

/-- The first explicit cubic source works on the larger rational interval
[4/11,3/8]; the estimates are exact Bernstein certificates. -/
theorem cubic_low_source_geometry {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ 3 / 8) :
    let lower := 1 - ratio + ratio ^ 2 - ratio ^ 3
    let upper := 1 - ratio + ratio ^ 2 - ratio ^ 3 + ratio ^ 4
    TwoBandInterval ratio (1 / upper ^ 2) (1 / lower ^ 2) ∧
      lower ^ 3 < 3 * ratio ^ 2 ∧ 3 * ratio ^ 2 * (1 - ratio ^ 2) < upper ^ 3 := by
  dsimp only
  have hpositive : 0 < ratio := by linarith
  have hhalf : ratio < 1 / 2 := by linarith
  have hbase : 0 < 1 - ratio + ratio ^ 2 - ratio ^ 3 := by
    nlinarith [mul_pos (sq_pos_of_pos hpositive) (show 0 < 1 - ratio by linarith)]
  refine ⟨inverse_square_second_band hpositive hhalf hbase
    (by nlinarith [pow_nonneg hpositive.le 4]) ?_ ?_ ?_, ?_, ?_⟩
  · nlinarith [cubic_low_above_one_certificate hlower hupper]
  · nlinarith [cubic_low_band_lower_certificate hlower hupper]
  · nlinarith [cubic_low_band_upper_certificate hlower hupper]
  · nlinarith [cubic_low_lower_corner_certificate hlower hupper]
  · nlinarith [cubic_low_upper_corner_certificate hlower hupper]

theorem cubic_high_source_geometry {ratio : ℝ}
    (hlower : (3 / 8 : ℝ) ≤ ratio) (hupper : ratio < 1 / 2) :
    let lower := 1 - ratio + ratio ^ 2 - ratio ^ 3
    let upper := 1 - ratio + ratio ^ 2
    TwoBandInterval ratio (1 / upper ^ 2) (1 / lower ^ 2) ∧
      lower ^ 3 < 3 * ratio ^ 2 ∧ 3 * ratio ^ 2 * (1 - ratio) < upper ^ 3 := by
  dsimp only
  have hpositive : 0 < ratio := by linarith
  have hbase : 0 < 1 - ratio + ratio ^ 2 - ratio ^ 3 := by
    nlinarith [mul_pos (sq_pos_of_pos hpositive) (show 0 < 1 - ratio by linarith)]
  refine ⟨inverse_square_second_band hpositive hupper hbase
    (by nlinarith [pow_nonneg hpositive.le 3]) ?_ ?_ ?_, ?_, ?_⟩
  · nlinarith [cubic_high_above_one_certificate hlower hupper.le]
  · nlinarith [cubic_high_band_lower_certificate hlower hupper.le]
  · nlinarith [cubic_high_band_upper_certificate hlower hupper.le]
  · nlinarith [cubic_high_lower_corner_certificate hlower hupper.le]
  · nlinarith [cubic_high_upper_corner_certificate hlower hupper.le]

theorem quadratic_low_source_geometry {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ 147 / 400) :
    let lower := 1 - ratio + ratio ^ 3 - ratio ^ 4
    let upper := 1 - ratio + ratio ^ 3
    TwoBandInterval ratio (1 / upper) (1 / lower) ∧
      lower ^ 2 < 2 * ratio * upper ∧ 2 * ratio * (1 - ratio) < upper ^ 2 := by
  dsimp only
  have hpositive : 0 < ratio := by linarith
  refine ⟨inverse_first_band hpositive (by linarith) ?_
    (by nlinarith [pow_nonneg hpositive.le 4]) ?_ ?_, ?_, ?_⟩
  · nlinarith [quadratic_low_above_complement_certificate hlower hupper]
  · nlinarith [quadratic_low_below_one_certificate hlower hupper]
  · nlinarith [quadratic_low_band_lower_certificate hlower hupper]
  · nlinarith [quadratic_low_lower_corner_certificate hlower hupper]
  · nlinarith [quadratic_low_upper_corner_certificate hlower hupper]

theorem quadratic_middle_source_geometry {ratio : ℝ}
    (hlower : (147 / 400 : ℝ) ≤ ratio) (hupper : ratio ≤ 3 / 8) :
    let lower := 1 - ratio + ratio ^ 2 - ratio ^ 3
    let upper := 1 - ratio + ratio ^ 2 - ratio ^ 3 + ratio ^ 4
    TwoBandInterval ratio (1 / upper) (1 / lower) ∧
      lower ^ 2 < 2 * ratio * (1 - ratio + ratio ^ 2) ∧
      2 * ratio * lower < upper ^ 2 := by
  dsimp only
  have hpositive : 0 < ratio := by linarith
  refine ⟨inverse_first_band hpositive (by linarith) ?_
    (by nlinarith [pow_nonneg hpositive.le 4]) ?_ ?_, ?_, ?_⟩
  · nlinarith [quadratic_middle_above_complement_certificate hlower hupper]
  · nlinarith [quadratic_middle_below_one_certificate hlower hupper]
  · nlinarith [quadratic_middle_band_lower_certificate hlower hupper]
  · nlinarith [quadratic_middle_lower_corner_certificate hlower hupper]
  · nlinarith [quadratic_middle_upper_corner_certificate hlower hupper]

theorem quadratic_high_source_geometry {ratio : ℝ}
    (hlower : (3 / 8 : ℝ) ≤ ratio) (hupper : ratio < 1 / 2) :
    let lower := 1 - ratio + ratio ^ 2 - ratio ^ 3
    let upper := 1 - ratio + ratio ^ 2
    TwoBandInterval ratio (1 / upper) (1 / lower) ∧
      lower ^ 2 < 2 * ratio * upper ∧ 2 * ratio * (1 - ratio) < upper ^ 2 := by
  dsimp only
  have hpositive : 0 < ratio := by linarith
  refine ⟨inverse_first_band hpositive hupper ?_
    (by nlinarith [pow_nonneg hpositive.le 3]) ?_ ?_, ?_, ?_⟩
  · nlinarith [quadratic_high_above_complement_certificate hlower hupper.le]
  · nlinarith [quadratic_high_below_one_certificate hlower hupper.le]
  · nlinarith [quadratic_high_band_lower_certificate hlower hupper.le]
  · nlinarith [quadratic_high_lower_corner_certificate hlower hupper.le]
  · nlinarith [quadratic_high_upper_corner_certificate hlower hupper.le]

end LambdaCantor.Last
