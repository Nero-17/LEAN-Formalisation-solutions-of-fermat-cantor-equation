import LambdaCantor.AE.SeriesTransversality
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace LambdaCantor.AE

/-- The factor lost when normalizing a pair of digit sequences whose first
difference is at the indicated depth. -/
noncomputable def firstDifferencePrefactor (depth : ℕ) (ratio : ℝ) : ℝ :=
  (1 - ratio) * ratio ^ depth

theorem hasDerivAt_firstDifferencePrefactor (depth : ℕ) (ratio : ℝ) :
    HasDerivAt (firstDifferencePrefactor depth)
      (-(ratio ^ depth) + (1 - ratio) * (depth : ℝ) * ratio ^ (depth - 1)) ratio := by
  convert ((hasDerivAt_const ratio (1 : ℝ)).sub (hasDerivAt_id ratio)).mul
    (hasDerivAt_pow depth ratio) using 1 <;>
    first | rfl | (dsimp [firstDifferencePrefactor]; ring)

theorem firstDifferencePrefactor_pos (depth : ℕ) {ratio : ℝ}
    (hpos : 0 < ratio) (hlt : ratio < 1) :
    0 < firstDifferencePrefactor depth ratio := by
  unfold firstDifferencePrefactor
  exact mul_pos (sub_pos.mpr hlt) (pow_pos hpos depth)

/-- The second prefactor derivative formula is valid also for depths zero and
one: the corresponding natural falling-factorial coefficients vanish. -/
theorem hasDerivAt_deriv_firstDifferencePrefactor (depth : ℕ) (ratio : ℝ) :
    HasDerivAt (deriv (firstDifferencePrefactor depth))
      (-2 * (depth : ℝ) * ratio ^ (depth - 1) +
        (1 - ratio) * (depth : ℝ) * (depth - 1 : ℕ) * ratio ^ (depth - 2)) ratio := by
  rw [show deriv (firstDifferencePrefactor depth) =
    (fun parameter => -(parameter ^ depth) +
      (1 - parameter) * (depth : ℝ) * parameter ^ (depth - 1)) from
        funext (fun parameter => (hasDerivAt_firstDifferencePrefactor depth parameter).deriv)]
  have hfirst := (hasDerivAt_pow depth ratio).neg
  have hsecond := (((hasDerivAt_const ratio (1 : ℝ)).sub (hasDerivAt_id ratio)).mul_const
    (depth : ℝ)).mul (hasDerivAt_pow (depth - 1) ratio)
  convert hfirst.add hsecond using 1 <;> first | rfl |
    (simp only [Pi.sub_apply, Pi.mul_apply, id_eq, Nat.sub_sub,
      show 1 + 1 = 2 from rfl]; ring)

/-- This bound includes depth zero. Its factor depth+1 explains why the
small-value band in the manuscript contains that divisor. -/
theorem firstDifferencePrefactor_derivative_bound (depth : ℕ)
    {lower ratio : ℝ} (hlower : 0 < lower) (horder : lower ≤ ratio) (hlt : ratio < 1) :
    |deriv (firstDifferencePrefactor depth) ratio| ≤
      ((depth + 1 : ℕ) : ℝ) / lower * ratio ^ depth := by
  have hpos := hlower.trans_le horder
  have hpower : 0 ≤ (depth : ℝ) * ratio ^ (depth - 1) := by positivity
  have hidentity : ratio * ((depth : ℝ) * ratio ^ (depth - 1)) =
      (depth : ℝ) * ratio ^ depth := by
    cases depth with
    | zero => simp
    | succ depth => simp only [Nat.succ_sub_one, pow_succ]; ring
  have hweighted : (depth : ℝ) * ratio ^ (depth - 1) ≤
      (depth : ℝ) / lower * ratio ^ depth := by
    have hmul := mul_le_mul_of_nonneg_right horder hpower
    rw [hidentity] at hmul
    calc
      (depth : ℝ) * ratio ^ (depth - 1) ≤ ((depth : ℝ) * ratio ^ depth) / lower :=
        (le_div_iff₀ hlower).mpr (by simpa only [mul_comm] using hmul)
      _ = (depth : ℝ) / lower * ratio ^ depth := by ring
  rw [(hasDerivAt_firstDifferencePrefactor depth ratio).deriv]
  calc
    |-(ratio ^ depth) + (1 - ratio) * (depth : ℝ) * ratio ^ (depth - 1)|
        ≤ |-(ratio ^ depth)| + |(1 - ratio) * (depth : ℝ) * ratio ^ (depth - 1)| := abs_add_le _ _
    _ = ratio ^ depth + (1 - ratio) * ((depth : ℝ) * ratio ^ (depth - 1)) := by
      rw [abs_neg, abs_of_nonneg (pow_nonneg hpos.le depth), abs_of_nonneg (by positivity)]
      ring
    _ ≤ ratio ^ depth + (depth : ℝ) / lower * ratio ^ depth := by
      have hmul := mul_le_mul_of_nonneg_right (show 1 - ratio ≤ 1 by linarith) hpower
      nlinarith
    _ ≤ ((depth + 1 : ℕ) : ℝ) / lower * ratio ^ depth := by
      have hlowone : lower ≤ 1 := horder.trans hlt.le
      have hinverse : 1 ≤ 1 / lower := (le_div_iff₀ hlower).mpr (by simpa using hlowone)
      have hpow := mul_le_mul_of_nonneg_right hinverse (pow_nonneg hpos.le depth)
      simp only [one_mul] at hpow
      calc
        _ ≤ (1 / lower) * ratio ^ depth + (depth : ℝ) / lower * ratio ^ depth :=
          add_le_add hpow (le_refl _)
        _ = _ := by push_cast; ring

/-- Exact differentiation of the actual digit difference, including its
nonzero leading digit and the (1-ratio) factor. -/
theorem hasDerivAt_digitResidual (depth : ℕ) (digit : ℝ)
    {function : ℝ → ℝ} {derivative ratio : ℝ} (hfunction : HasDerivAt function derivative ratio) :
    HasDerivAt (fun parameter => digit * firstDifferencePrefactor depth parameter * function parameter)
      (digit * (deriv (firstDifferencePrefactor depth) ratio * function ratio +
        firstDifferencePrefactor depth ratio * derivative)) ratio := by
  have hprefactor := hasDerivAt_firstDifferencePrefactor depth ratio
  rw [← hprefactor.deriv] at hprefactor
  convert (hprefactor.mul hfunction).const_mul digit using 1 <;>
    first | rfl | (funext parameter; simp only [Pi.mul_apply]; ring) | ring

/-- Exact second derivative of the actual residual. The global first-derivative
identity is stated explicitly, so differentiating an equality known at only
one parameter is never used. -/
theorem hasDerivAt_deriv_digitResidual (depth : ℕ) (digit : ℝ)
    {function firstDerivative : ℝ → ℝ} {secondDerivative ratio : ℝ}
    (hfunction : ∀ parameter, HasDerivAt function (firstDerivative parameter) parameter)
    (hfirst : HasDerivAt firstDerivative secondDerivative ratio) :
    HasDerivAt
      (deriv (fun parameter => digit * firstDifferencePrefactor depth parameter * function parameter))
      (digit * (deriv (deriv (firstDifferencePrefactor depth)) ratio * function ratio +
        2 * deriv (firstDifferencePrefactor depth) ratio * firstDerivative ratio +
        firstDifferencePrefactor depth ratio * secondDerivative)) ratio := by
  rw [show deriv (fun parameter => digit * firstDifferencePrefactor depth parameter * function parameter) =
      (fun parameter => digit * (deriv (firstDifferencePrefactor depth) parameter * function parameter +
        firstDifferencePrefactor depth parameter * firstDerivative parameter)) from
      funext (fun parameter => (hasDerivAt_digitResidual depth digit (hfunction parameter)).deriv)]
  have hprefactor := hasDerivAt_firstDifferencePrefactor depth ratio
  rw [← hprefactor.deriv] at hprefactor
  have hsecond := hasDerivAt_deriv_firstDifferencePrefactor depth ratio
  rw [← hsecond.deriv] at hsecond
  convert ((hsecond.mul (hfunction ratio)).add (hprefactor.mul hfirst)).const_mul digit using 1 <;>
    first | rfl | (funext parameter; simp only [Pi.mul_apply, Pi.add_apply]; ring) |
      (try simp only [Pi.mul_apply, Pi.add_apply]; ring)
  all_goals ring

/-- The actual small-value band implies a bound on the normalized value.
The depth divisor survives normalization and cancels the prefactor derivative
growth in the next theorem. -/
theorem normalized_value_small_of_digitResidual_small
    (depth : ℕ) {digit lower upper ratio value epsilon : ℝ}
    (hdigit : 1 ≤ |digit|) (hlower : 0 < lower)
    (hratio : ratio ∈ Set.Icc lower upper) (hupper : upper < 1)
    (hsmall : |digit * firstDifferencePrefactor depth ratio * value| <
      epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)) :
    |value| < epsilon / ((1 - upper) * ((depth + 1 : ℕ) : ℝ)) := by
  have hpos := hlower.trans_le hratio.1
  have hratioone := hratio.2.trans_lt hupper
  have hgap : 0 < 1 - upper := sub_pos.mpr hupper
  have hdepth : (0 : ℝ) < ((depth + 1 : ℕ) : ℝ) := by positivity
  have hpow : 0 < lower ^ depth := pow_pos hlower depth
  have hprefactor := firstDifferencePrefactor_pos depth hpos hratioone
  have hprefactorLower : (1 - upper) * lower ^ depth ≤ firstDifferencePrefactor depth ratio := by
    unfold firstDifferencePrefactor
    apply mul_le_mul (by linarith [hratio.2])
      (pow_le_pow_left₀ hlower.le hratio.1 depth) (pow_nonneg hlower.le depth)
      (by linarith)
  have habslower : (1 - upper) * lower ^ depth * |value| ≤
      |digit * firstDifferencePrefactor depth ratio * value| := by
    rw [abs_mul, abs_mul, abs_of_pos hprefactor]
    have hfirst : firstDifferencePrefactor depth ratio ≤
        |digit| * firstDifferencePrefactor depth ratio := by nlinarith
    exact mul_le_mul_of_nonneg_right (hprefactorLower.trans hfirst) (abs_nonneg value)
  have hband := (lt_div_iff₀ hdepth).mp hsmall
  have hmultiplied := mul_le_mul_of_nonneg_right habslower hdepth.le
  have hcancel : lower ^ depth * ((1 - upper) * |value| * ((depth + 1 : ℕ) : ℝ)) <
      lower ^ depth * epsilon := by nlinarith
  have hnormalized := (mul_lt_mul_iff_of_pos_left hpow).mp hcancel
  apply (lt_div_iff₀ (mul_pos hgap hdepth)).mpr
  nlinarith

/-- Quantitative dominance of the transverse normalized term over the
derivative of its first-difference prefactor. The small-value bound here is
the normalized form of equation (small-value-band). -/
theorem digitResidual_derivative_negative
    (depth : ℕ) {lower upper ratio margin value derivative : ℝ}
    (hlower : 0 < lower) (hratio : ratio ∈ Set.Icc lower upper) (hupper : upper < 1)
    (hmargin : 0 < margin) (hderivative : derivative ≤ -margin)
    (hsmall : |value| ≤ margin * lower * (1 - upper) /
      (2 * ((depth + 1 : ℕ) : ℝ))) :
    deriv (firstDifferencePrefactor depth) ratio * value +
      firstDifferencePrefactor depth ratio * derivative ≤
        -(margin * (1 - upper) / 2) * ratio ^ depth := by
  have hpos := hlower.trans_le hratio.1
  have hratioone : ratio < 1 := hratio.2.trans_lt hupper
  have hdepth : (0 : ℝ) < ((depth + 1 : ℕ) : ℝ) := by positivity
  have hprefactor := (firstDifferencePrefactor_pos depth hpos hratioone).le
  have hprod := mul_le_mul_of_nonneg_left hderivative hprefactor
  have habs := mul_le_mul
    (firstDifferencePrefactor_derivative_bound depth hlower hratio.1 hratioone)
    hsmall (abs_nonneg value) (by positivity)
  have hnormal : (((depth + 1 : ℕ) : ℝ) / lower * ratio ^ depth) *
      (margin * lower * (1 - upper) / (2 * ((depth + 1 : ℕ) : ℝ))) =
        margin * (1 - upper) / 2 * ratio ^ depth := by
    field_simp [hlower.ne', hdepth.ne']
    <;> ring
  rw [hnormal] at habs
  have hterm := (le_abs_self (deriv (firstDifferencePrefactor depth) ratio * value)).trans
    (by simpa only [abs_mul] using habs)
  have hgap : margin * (1 - upper) * ratio ^ depth ≤
      margin * (1 - ratio) * ratio ^ depth := by
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hpos.le depth)
    exact mul_le_mul_of_nonneg_left (by linarith [hratio.2]) hmargin.le
  unfold firstDifferencePrefactor at hprod hterm ⊢
  nlinarith

end LambdaCantor.AE
