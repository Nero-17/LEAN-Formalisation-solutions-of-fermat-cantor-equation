import LambdaCantor.Integer.FixedSignedLog

namespace LambdaCantor.Integer

def IntInterval.scaleBy (bounds : IntInterval) (coefficient : ℕ) : IntInterval :=
  ⟨coefficient*bounds.lower,coefficient*bounds.upper⟩

theorem IntInterval.scaleBy_sound {scale coefficient : ℕ} {bounds : IntInterval}
    {value : ℝ} (enclosed : bounds.Encloses scale value) :
    (bounds.scaleBy coefficient).Encloses scale ((coefficient : ℝ)*value) := by
  have lower := mul_le_mul_of_nonneg_left enclosed.1
    (show (0 : ℝ) ≤ coefficient by positivity)
  have upper := mul_le_mul_of_nonneg_left enclosed.2
    (show (0 : ℝ) ≤ coefficient by positivity)
  unfold IntInterval.Encloses IntInterval.scaleBy
  push_cast
  constructor <;> nlinarith

def IntInterval.divideBetween (numerator denominator : IntInterval) : IntInterval :=
  ⟨min (numerator.lower/denominator.lower) (numerator.lower/denominator.upper),
    max (numerator.upper/denominator.lower) (numerator.upper/denominator.upper)+1⟩

theorem IntInterval.divideBetween_sound (scale : ℕ) (scalePositive : 0 < scale)
    (numerator denominator : IntInterval)
    (lowerPositive : 0 < denominator.lower) (upperPositive : 0 < denominator.upper)
    (x y : ℝ) (yPositive : 0 < y)
    (xEnclosed : numerator.Encloses scale x) (yEnclosed : denominator.Encloses scale y) :
    (numerator.divideBetween denominator).Encloses 1 (x/y) := by
  have lowerFirst := Int.ediv_mul_le numerator.lower (ne_of_gt lowerPositive)
  have lowerSecond := Int.ediv_mul_le numerator.lower (ne_of_gt upperPositive)
  have upperFirst := Int.lt_ediv_add_one_mul_self numerator.upper lowerPositive
  have upperSecond := Int.lt_ediv_add_one_mul_self numerator.upper upperPositive
  have lowerMinFirst := mul_le_mul_of_nonneg_right
    (min_le_left (numerator.lower/denominator.lower) (numerator.lower/denominator.upper))
    lowerPositive.le
  have lowerMinSecond := mul_le_mul_of_nonneg_right
    (min_le_right (numerator.lower/denominator.lower) (numerator.lower/denominator.upper))
    upperPositive.le
  have upperMaxFirst := mul_le_mul_of_nonneg_right
    (add_le_add_right (le_max_left (numerator.upper/denominator.lower)
      (numerator.upper/denominator.upper)) 1) lowerPositive.le
  have upperMaxSecond := mul_le_mul_of_nonneg_right
    (add_le_add_right (le_max_right (numerator.upper/denominator.lower)
      (numerator.upper/denominator.upper)) 1) upperPositive.le
  have upperFirstBound : numerator.upper ≤
      (numerator.divideBetween denominator).upper*denominator.lower := by
    exact upperFirst.le.trans (by
      simpa only [IntInterval.divideBetween, add_comm] using upperMaxFirst)
  have upperSecondBound : numerator.upper ≤
      (numerator.divideBetween denominator).upper*denominator.upper := by
    exact upperSecond.le.trans (by
      simpa only [IntInterval.divideBetween, add_comm] using upperMaxSecond)
  have result := fixed_division_bounds scale scalePositive x y yPositive numerator denominator
    xEnclosed yEnclosed (numerator.divideBetween denominator).lower
    (numerator.divideBetween denominator).upper
    (lowerMinFirst.trans lowerFirst) (lowerMinSecond.trans lowerSecond)
    upperFirstBound upperSecondBound
  simpa only [IntInterval.Encloses,Nat.cast_one,one_mul] using result

def rationalLatticeInterval (scale : ℕ) (numerator : ℤ) (denominator : ℕ) : IntInterval :=
  ⟨(scale : ℤ)*numerator/denominator,(scale : ℤ)*numerator/denominator+1⟩

theorem rationalLatticeInterval_sound (scale : ℕ) (numerator : ℤ) (denominator : ℕ)
    (positive : 0 < denominator) :
    (rationalLatticeInterval scale numerator denominator).Encloses scale
      ((numerator : ℝ)/denominator) := by
  have denominatorIntPositive : (0 : ℤ) < denominator := by exact_mod_cast positive
  have denominatorRealPositive : (0 : ℝ) < denominator := by exact_mod_cast positive
  have lower := Int.ediv_mul_le ((scale : ℤ)*numerator) (ne_of_gt denominatorIntPositive)
  have upper := (Int.lt_ediv_add_one_mul_self ((scale : ℤ)*numerator)
    denominatorIntPositive).le
  have lowerReal : (((scale : ℤ)*numerator/denominator : ℤ) : ℝ)*denominator ≤
      (scale : ℝ)*numerator := by exact_mod_cast lower
  have upperReal : (scale : ℝ)*numerator ≤
      ((((scale : ℤ)*numerator/denominator : ℤ)+1 : ℤ) : ℝ)*denominator := by
    exact_mod_cast upper
  unfold IntInterval.Encloses rationalLatticeInterval
  dsimp only
  simp only [← mul_div_assoc]
  exact ⟨(le_div_iff₀ denominatorRealPositive).2 lowerReal,
    (div_le_iff₀ denominatorRealPositive).2 upperReal⟩

end LambdaCantor.Integer
