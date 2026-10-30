import LambdaCantor.RationalPowers.CoarseSources

namespace LambdaCantor.RationalPowers
open Integer

def CoarseSourceRow.StaticChecked (row : CoarseSourceRow) : Prop :=
  0 < row.horizontal ∧ 0 < row.vertical ∧
  ternaryPrefix row.horizontal 7 = true ∧ ternaryPrefix row.vertical 7 = true

instance (row : CoarseSourceRow) : Decidable row.StaticChecked := by
  unfold CoarseSourceRow.StaticChecked
  infer_instance

/-- The denominator-dependent width comparison after clearing only positive
factors. Finite classification evaluates these natural products, avoiding Rat
normalization at each of eight million candidate exponents. -/
def CoarseSourceRow.IntegerWidthChecked (row : CoarseSourceRow) (numerator denominator shift : ℕ) : Prop :=
  0 < numerator ∧ 0 < denominator ∧
  11*3^shift*(row.horizontal+1)*(row.vertical+1) <
    10*(numerator*(row.vertical+1)+denominator*3^shift*(row.horizontal+1))

instance (row : CoarseSourceRow) (numerator denominator shift : ℕ) :
    Decidable (row.IntegerWidthChecked numerator denominator shift) := by
  unfold CoarseSourceRow.IntegerWidthChecked
  infer_instance

/-- The executable integer-width predicate implies the exact rational width
input of the proved logarithm/phase construction. A full band check remains
separate and is not a consequence of this width theorem. -/
theorem CoarseSourceRow.IntegerWidthChecked.widthAccepted {row : CoarseSourceRow}
    {numerator denominator shift : ℕ} (static : row.StaticChecked)
    (checked : row.IntegerWidthChecked numerator denominator shift) :
    row.WidthAccepted numerator denominator shift := by
  obtain ⟨horizontal_positive,vertical_positive,horizontal_prefix,vertical_prefix⟩ := static
  obtain ⟨numerator_positive,denominator_positive,width⟩ := checked
  refine ⟨numerator_positive,denominator_positive,horizontal_positive,vertical_positive,
    horizontal_prefix,vertical_prefix,?_⟩
  have denominator_rat_positive : (0 : ℚ) < denominator := by exact_mod_cast denominator_positive
  have scale_positive : (0 : ℚ) < (3 : ℚ)^shift := by positivity
  have horizontal_next_positive : (0 : ℚ) < (row.horizontal : ℚ)+1 := by positivity
  have vertical_next_positive : (0 : ℚ) < (row.vertical : ℚ)+1 := by positivity
  have width_rat : (11 : ℚ)*3^shift*(row.horizontal+1)*(row.vertical+1) <
      10*((numerator : ℚ)*(row.vertical+1)+denominator*3^shift*(row.horizontal+1)) := by exact_mod_cast width
  have cleared_identity :
      (((((numerator : ℚ)/denominator)/3^shift)/(row.horizontal+1)+1/(row.vertical+1))-
        11/(10*(denominator : ℚ)))*(10*denominator*3^shift*(row.horizontal+1)*(row.vertical+1)) =
      10*((numerator : ℚ)*(row.vertical+1)+denominator*3^shift*(row.horizontal+1))-
        11*3^shift*(row.horizontal+1)*(row.vertical+1) := by
    field_simp [denominator_rat_positive.ne',scale_positive.ne',horizontal_next_positive.ne',vertical_next_positive.ne']
    <;> ring
  have product_positive : 0 <
      (((((numerator : ℚ)/denominator)/3^shift)/(row.horizontal+1)+1/(row.vertical+1))-
        11/(10*(denominator : ℚ)))*(10*denominator*3^shift*(row.horizontal+1)*(row.vertical+1)) := by
    rw [cleared_identity]
    exact sub_pos.mpr width_rat
  apply sub_pos.mp
  by_contra absent
  have nonpositive : (((numerator : ℚ)/denominator)/3^shift)/(row.horizontal+1)+1/(row.vertical+1)-
      11/(10*(denominator : ℚ)) ≤ 0 := le_of_not_gt absent
  have product_nonpositive := mul_nonpos_of_nonpos_of_nonneg nonpositive
    (show (0 : ℚ) ≤ 10*denominator*3^shift*(row.horizontal+1)*(row.vertical+1) by positivity)
  linarith

end LambdaCantor.RationalPowers
