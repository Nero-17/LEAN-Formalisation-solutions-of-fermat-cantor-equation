import LambdaCantor.First.AddressParameter
import LambdaCantor.First.RationalNormalization
import Mathlib.Tactic.Positivity

noncomputable section
namespace LambdaCantor.First

/-- Parameterized left full-tail factor in the powers-four cylinders. -/
def powersFourLeftFactor (padding : ℕ) (digits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  1 - ratio ^ padding + ratio ^ padding * address ratio digits

/-- Parameterized right full-tail factor in the powers-four cylinders. -/
def powersFourRightFactor (padding : ℕ) (digits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  1 - ratio ^ padding * address ratio digits

theorem hasDerivAt_powersFourLeftFactor {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1)
    (padding : ℕ) (digits : ℕ → Bool) :
    HasDerivAt (powersFourLeftFactor padding digits)
      ((padding : ℝ) * ratio ^ (padding - 1) * (address ratio digits - 1) +
        ratio ^ padding * addressParameterDerivative ratio digits) ratio := by
  have hpower := (hasDerivAt_id ratio).pow padding
  have haddress := hasDerivAt_address_parameter hpos hlt digits
  convert! ((hasDerivAt_const ratio (1 : ℝ)).sub hpower).add
    (hpower.mul haddress) using 1 <;> (try dsimp only [powersFourLeftFactor, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq]) <;> ring

theorem hasDerivAt_powersFourRightFactor {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1)
    (padding : ℕ) (digits : ℕ → Bool) :
    HasDerivAt (powersFourRightFactor padding digits)
      (-((padding : ℝ) * ratio ^ (padding - 1) * address ratio digits +
        ratio ^ padding * addressParameterDerivative ratio digits)) ratio := by
  have hpower := (hasDerivAt_id ratio).pow padding
  have haddress := hasDerivAt_address_parameter hpos hlt digits
  convert! (hasDerivAt_const ratio (1 : ℝ)).sub (hpower.mul haddress) using 1 <;>
    (try dsimp only [powersFourRightFactor, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq]) <;> ring

/-- A common bound for the derivative of a scaled tail or its complement. -/
theorem scaled_tail_derivative_bound {ratio upper tail tailDerivative : ℝ}
    (hratio : 0 ≤ ratio) (hratioUpper : ratio ≤ upper) (hupper : upper < 1)
    (htail : |tail| ≤ 1)
    (hderivative : |tailDerivative| ≤ addressParameterDerivativeBound upper)
    (padding : ℕ) :
    |(padding : ℝ) * ratio ^ (padding - 1) * tail + ratio ^ padding * tailDerivative| ≤
      (padding : ℝ) * upper ^ (padding - 1) +
        upper ^ padding * addressParameterDerivativeBound upper := by
  have hboundNonneg : 0 ≤ addressParameterDerivativeBound upper :=
    (abs_nonneg tailDerivative).trans hderivative
  have hfirst : |(padding : ℝ) * ratio ^ (padding - 1) * tail| ≤
      (padding : ℝ) * upper ^ (padding - 1) := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hratio _))]
    calc
      _ ≤ (padding : ℝ) * ratio ^ (padding - 1) * 1 :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ _ := by
        simpa using mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hratio hratioUpper (padding - 1)) (Nat.cast_nonneg padding)
  have hsecond : |ratio ^ padding * tailDerivative| ≤
      upper ^ padding * addressParameterDerivativeBound upper := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hratio _)]
    exact (mul_le_mul_of_nonneg_left hderivative (pow_nonneg hratio _)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hratio hratioUpper padding) hboundNonneg)
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

/-- Both full-tail factors remain in the unit interval. -/
theorem powersFour_factors_mem_unit {ratio : ℝ} (hpos : 0 ≤ ratio) (hlt : ratio < 1)
    (padding : ℕ) (digits : ℕ → Bool) :
    powersFourLeftFactor padding digits ratio ∈ Set.Icc (0 : ℝ) 1 ∧
    powersFourRightFactor padding digits ratio ∈ Set.Icc (0 : ℝ) 1 := by
  have haddress0 := address_nonnegative hpos hlt digits
  have haddress1 := address_le_one hpos hlt digits
  have hpower0 := pow_nonneg hpos padding
  have hpower1 := pow_le_one₀ hpos hlt.le (n := padding)
  have hproduct0 := mul_nonneg hpower0 haddress0
  have hproduct1 := mul_le_mul_of_nonneg_left haddress1 hpower0
  unfold powersFourLeftFactor powersFourRightFactor
  constructor <;> constructor <;> nlinarith

/-- Actual left-factor derivative bound, uniform in the full binary tail. -/
theorem powersFourLeftFactor_derivative_bound {ratio upper : ℝ}
    (hpos : 0 < ratio) (hratioUpper : ratio ≤ upper) (hupper : upper < 1)
    (padding : ℕ) (digits : ℕ → Bool) :
    |deriv (powersFourLeftFactor padding digits) ratio| ≤
      (padding : ℝ) * upper ^ (padding - 1) +
        upper ^ padding * addressParameterDerivativeBound upper := by
  have hlt := hratioUpper.trans_lt hupper
  rw [(hasDerivAt_powersFourLeftFactor hpos hlt padding digits).deriv]
  apply scaled_tail_derivative_bound hpos.le hratioUpper hupper _
    (address_parameter_derivative_bound hpos.le hratioUpper hupper digits) padding
  apply abs_le.mpr
  have h0 := address_nonnegative hpos.le hlt digits
  have h1 := address_le_one hpos.le hlt digits
  constructor <;> linarith

/-- Actual right-factor derivative bound, uniform in the full binary tail. -/
theorem powersFourRightFactor_derivative_bound {ratio upper : ℝ}
    (hpos : 0 < ratio) (hratioUpper : ratio ≤ upper) (hupper : upper < 1)
    (padding : ℕ) (digits : ℕ → Bool) :
    |deriv (powersFourRightFactor padding digits) ratio| ≤
      (padding : ℝ) * upper ^ (padding - 1) +
        upper ^ padding * addressParameterDerivativeBound upper := by
  have hlt := hratioUpper.trans_lt hupper
  rw [(hasDerivAt_powersFourRightFactor hpos hlt padding digits).deriv, abs_neg]
  apply scaled_tail_derivative_bound hpos.le hratioUpper hupper _
    (address_parameter_derivative_bound hpos.le hratioUpper hupper digits) padding
  rw [abs_of_nonneg (address_nonnegative hpos.le hlt digits)]
  exact address_le_one hpos.le hlt digits

/-- Both factors approach one at the exact tail scale, uniformly in digits. -/
theorem powersFour_factor_deviation_bound {ratio upper : ℝ}
    (hpos : 0 ≤ ratio) (hratioUpper : ratio ≤ upper) (hupper : upper < 1)
    (padding : ℕ) (digits : ℕ → Bool) :
    |powersFourLeftFactor padding digits ratio - 1| ≤ upper ^ padding ∧
    |powersFourRightFactor padding digits ratio - 1| ≤ upper ^ padding := by
  have hlt := hratioUpper.trans_lt hupper
  have hunit := powersFour_factors_mem_unit hpos hlt padding digits
  have haddress0 := address_nonnegative hpos hlt digits
  have haddress1 := address_le_one hpos hlt digits
  have hpower0 := pow_nonneg hpos padding
  have hpowerUpper := pow_le_pow_left₀ hpos hratioUpper padding
  have hproduct0 := mul_nonneg hpower0 haddress0
  have hproduct1 := mul_le_mul_of_nonneg_left haddress1 hpower0
  constructor
  · rw [abs_of_nonpos (sub_nonpos.mpr hunit.1.2)]
    unfold powersFourLeftFactor
    nlinarith
  · rw [abs_of_nonpos (sub_nonpos.mpr hunit.2.2)]
    unfold powersFourRightFactor
    nlinarith

/-- The derivative bound for each finite binomial remainder term. This
applies in particular to the actual signed right full-tail factor. -/
theorem scaled_power_derivative_bound
    (depth power : ℕ) (tail : ℝ → ℝ) {ratio upper tailDerivative derivativeBound : ℝ}
    (hratio : 0 ≤ ratio) (hratioUpper : ratio ≤ upper)
    (htailDerivative : HasDerivAt tail tailDerivative ratio)
    (htail : |tail ratio| ≤ 1) (hderivative : |tailDerivative| ≤ derivativeBound) :
    |deriv (fun parameter => parameter ^ depth * tail parameter ^ power) ratio| ≤
      (depth : ℝ) * upper ^ (depth - 1) +
        (power : ℝ) * upper ^ depth * derivativeBound := by
  have hbound0 : 0 ≤ derivativeBound := (abs_nonneg _).trans hderivative
  have hupper0 := hratio.trans hratioUpper
  have htailPower : |tail ratio| ^ power ≤ 1 := pow_le_one₀ (abs_nonneg _) htail
  have htailPowerPred : |tail ratio| ^ (power - 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) htail
  have hmain : HasDerivAt (fun parameter => parameter ^ depth * tail parameter ^ power)
      ((depth : ℝ) * ratio ^ (depth - 1) * tail ratio ^ power +
        ratio ^ depth * ((power : ℝ) * tail ratio ^ (power - 1) * tailDerivative)) ratio := by
    convert! ((hasDerivAt_id ratio).pow depth).mul (htailDerivative.pow power) using 1 <;>
      (try dsimp only [Pi.mul_apply, Pi.pow_apply, id_eq]) <;> ring
  rw [hmain.deriv]
  have hfirst : |(depth : ℝ) * ratio ^ (depth - 1) * tail ratio ^ power| ≤
      (depth : ℝ) * upper ^ (depth - 1) := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hratio _)), abs_pow]
    calc
      _ ≤ (depth : ℝ) * ratio ^ (depth - 1) * 1 :=
        mul_le_mul_of_nonneg_left htailPower (by positivity)
      _ ≤ _ := by
        simpa using mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hratio hratioUpper (depth - 1)) (Nat.cast_nonneg depth)
  have hinner : |(power : ℝ) * tail ratio ^ (power - 1) * tailDerivative| ≤
      (power : ℝ) * derivativeBound := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg power), abs_pow]
    calc
      _ ≤ (power : ℝ) * 1 * |tailDerivative| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htailPowerPred (Nat.cast_nonneg power)) (abs_nonneg _)
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hderivative (Nat.cast_nonneg power)
  have hsecond : |ratio ^ depth * ((power : ℝ) * tail ratio ^ (power - 1) * tailDerivative)| ≤
      (power : ℝ) * upper ^ depth * derivativeBound := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hratio depth)]
    calc
      _ ≤ ratio ^ depth * ((power : ℝ) * derivativeBound) :=
        mul_le_mul_of_nonneg_left hinner (pow_nonneg hratio depth)
      _ ≤ upper ^ depth * ((power : ℝ) * derivativeBound) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hratio hratioUpper depth)
          (mul_nonneg (Nat.cast_nonneg power) hbound0)
      _ = _ := by ring
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

end LambdaCantor.First


