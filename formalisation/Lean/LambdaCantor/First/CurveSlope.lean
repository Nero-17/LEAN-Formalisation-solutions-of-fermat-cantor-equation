import LambdaCantor.Curve
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor

def curveSlope (exponent point : ℝ) : ℝ :=
  -point ^ (exponent - 1) * (1 - point ^ exponent) ^ (exponent⁻¹ - 1)

theorem hasDerivAt_curveHeight {exponent point : ℝ} (hexponent : 0 < exponent)
    (hpoint : point ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun value : ℝ => (1 - value ^ exponent) ^ exponent⁻¹)
      (curveSlope exponent point) point := by
  have hbase : 0 < 1 - point ^ exponent :=
    sub_pos.mpr (Real.rpow_lt_one hpoint.1.le hpoint.2 hexponent)
  have hpower := (hasDerivAt_id point).rpow_const (p := exponent) (Or.inl hpoint.1.ne')
  convert! (((hasDerivAt_const point (1 : ℝ)).sub hpower).rpow_const
    (p := exponent⁻¹) (Or.inl hbase.ne')) using 1
  dsimp [curveSlope]
  field_simp [hexponent.ne']
  <;> ring

/-- The tangent slope of the positive power arc has a strictly negative
parameter derivative everywhere in its interior. -/
theorem curveSlope_hasDerivAt_negative {exponent point : ℝ} (hexponent : 1 < exponent)
    (hpoint : point ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ derivative : ℝ, derivative < 0 ∧ HasDerivAt (curveSlope exponent) derivative point := by
  have hexponent_pos : 0 < exponent := lt_trans zero_lt_one hexponent
  have hbase : 0 < 1 - point ^ exponent :=
    sub_pos.mpr (Real.rpow_lt_one hpoint.1.le hpoint.2 hexponent_pos)
  have hinverse : exponent⁻¹ - 1 < 0 := by
    have h := (inv_lt_one₀ hexponent_pos).mpr hexponent
    linarith
  have hleft : HasDerivAt (fun value : ℝ => value ^ (exponent - 1))
      ((exponent - 1) * point ^ ((exponent - 1) - 1)) point := by
    simpa only [one_mul] using! (hasDerivAt_id point).rpow_const
      (p := exponent - 1) (Or.inl hpoint.1.ne')
  have hpower : HasDerivAt (fun value : ℝ => value ^ exponent)
      (exponent * point ^ (exponent - 1)) point := by
    simpa only [one_mul] using! (hasDerivAt_id point).rpow_const
      (p := exponent) (Or.inl hpoint.1.ne')
  have hright : HasDerivAt (fun value : ℝ => (1 - value ^ exponent) ^ (exponent⁻¹ - 1))
      ((-exponent * point ^ (exponent - 1)) * (exponent⁻¹ - 1) *
        (1 - point ^ exponent) ^ ((exponent⁻¹ - 1) - 1)) point := by
    simpa only [zero_sub, neg_mul] using!
      ((hasDerivAt_const point (1 : ℝ)).sub hpower).rpow_const
        (p := exponent⁻¹ - 1) (Or.inl hbase.ne')
  have hleft_derivative : 0 < (exponent - 1) * point ^ ((exponent - 1) - 1) :=
    mul_pos (sub_pos.mpr hexponent) (Real.rpow_pos_of_pos hpoint.1 _)
  have hright_derivative : 0 < (-exponent * point ^ (exponent - 1)) * (exponent⁻¹ - 1) *
      (1 - point ^ exponent) ^ ((exponent⁻¹ - 1) - 1) :=
    mul_pos (mul_pos_of_neg_of_neg
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hexponent_pos) (Real.rpow_pos_of_pos hpoint.1 _))
      hinverse) (Real.rpow_pos_of_pos hbase _)
  refine ⟨_, neg_neg_of_pos (add_pos
    (mul_pos hleft_derivative (Real.rpow_pos_of_pos hbase (exponent⁻¹ - 1)))
    (mul_pos (Real.rpow_pos_of_pos hpoint.1 (exponent - 1)) hright_derivative)), ?_⟩
  convert! (hleft.mul hright).neg using 1
  funext value
  simp only [curveSlope, Pi.neg_apply, Pi.mul_apply, neg_mul]

end LambdaCantor

