import LambdaCantor.Last.AnalyticCoarseEndpointWitnessIntersection
import LambdaCantor.Last.AnalyticCoarseInfinitude
import Lean.Elab.Tactic.Omega

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

private theorem coarse_shell_scaled_mem {ratio coordinate : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio < 1) (depth : ℕ)
    (hcoordinate : coordinate ∈ cantorSet ratio) : ratio ^ depth * coordinate ∈ cantorSet ratio := by
  induction depth with
  | zero => simpa using hcoordinate
  | succ depth ih =>
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using low_copy_mem hratio hless ih

/-- The logarithmic equality supplies the actual power identity and actual
Cantor membership at every sufficiently deep rational shell. -/
theorem coarse_actual_rational_shell_point {ratio exponent first second : ℝ}
    (hratio : 0 < ratio) (hless : ratio < 1) (hexponent : 1 < exponent)
    {numerator denominator index : ℕ} (hphase : exponent * denominator = numerator)
    (shift : ℤ) (hdepth : 0 ≤ shift + (numerator * index : ℕ))
    (hfirst : first ∈ outerCantor ratio) (hsecond : second ∈ outerCantor ratio)
    (hdrop : 0 < coarseNormalizedPowerDrop exponent
      (ratio ^ (shift : ℝ) * ratio ^ (numerator * index)) second)
    (hequation : exponent * Real.log first = Real.log exponent - shift * (-Real.log ratio) +
      coarsePowerLog exponent (ratio ^ (shift : ℝ) * ratio ^ (numerator * index)) second) :
    ∃ point ∈ intersection exponent ratio,
      (1 - ratio) * ratio ^ (denominator * index) ≤ point.1 ∧
        point.1 ≤ ratio ^ (denominator * index) := by
  have hfirst_bounds := outerCantor_bounds hratio.le hless hfirst
  have hfirst_positive : 0 < first := by linarith [hfirst_bounds.1]
  have hexponent_positive : 0 < exponent := by linarith
  have hoffset_positive : 0 < ratio ^ (shift : ℝ) := Real.rpow_pos_of_pos hratio _
  have hscale_positive : 0 < ratio ^ (shift : ℝ) * ratio ^ (numerator * index) :=
    mul_pos hoffset_positive (pow_pos hratio _)
  have hscale_depth : ratio ^ (shift : ℝ) * ratio ^ (numerator * index) =
      ratio ^ (shift + (numerator * index : ℕ)).toNat := by
    rw [← Real.rpow_natCast ratio (numerator * index), ← Real.rpow_add hratio,
      ← Real.rpow_natCast ratio (shift + (numerator * index : ℕ)).toNat]
    congr 1
    have hcast := Int.toNat_of_nonneg hdepth
    exact_mod_cast hcast.symm
  have hpower : first ^ exponent = exponent * ratio ^ (shift : ℝ) *
      coarseNormalizedPowerDrop exponent (ratio ^ (shift : ℝ) * ratio ^ (numerator * index)) second := by
    apply Real.log_injOn_pos (Real.rpow_pos_of_pos hfirst_positive exponent)
      (mul_pos (mul_pos hexponent_positive hoffset_positive) hdrop)
    rw [Real.log_rpow hfirst_positive, Real.log_mul (mul_pos hexponent_positive hoffset_positive).ne' hdrop.ne',
      Real.log_mul hexponent_positive.ne' hoffset_positive.ne', Real.log_rpow hratio]
    change exponent * Real.log first = _ at hequation
    dsimp [coarsePowerLog] at hequation
    linarith
  have hscaled_power : (ratio ^ (denominator * index) * first) ^ exponent =
      ratio ^ (numerator * index) * first ^ exponent := by
    rw [Real.mul_rpow (pow_nonneg hratio.le _) hfirst_positive.le,
      ← Real.rpow_natCast_mul hratio.le]
    have hreal : ((denominator * index : ℕ) : ℝ) * exponent = ((numerator * index : ℕ) : ℝ) := by
      push_cast
      nlinarith [hphase]
    rw [hreal, Real.rpow_natCast]
  refine ⟨(ratio ^ (denominator * index) * first,
    1 - (ratio ^ (shift : ℝ) * ratio ^ (numerator * index)) * second), ?_, ?_, ?_⟩
  · refine ⟨coarse_shell_scaled_mem hratio.le hless _ (outerCantor_subset_cantorSet hratio.le hless hfirst), ?_, ?_⟩
    · rw [hscale_depth]
      exact one_sub_mem_cantorSet hratio.le hless
        (coarse_shell_scaled_mem hratio.le hless _ (outerCantor_subset_cantorSet hratio.le hless hsecond))
    · change (ratio ^ (denominator * index) * first) ^ exponent +
        (1 - (ratio ^ (shift : ℝ) * ratio ^ (numerator * index)) * second) ^ exponent = 1
      rw [hscaled_power, hpower]
      unfold coarseNormalizedPowerDrop
      field_simp [hexponent_positive.ne', hscale_positive.ne']
      <;> ring
  · change (1 - ratio) * ratio ^ (denominator * index) ≤ ratio ^ (denominator * index) * first
    nlinarith [mul_le_mul_of_nonneg_left hfirst_bounds.1 (pow_nonneg hratio.le (denominator * index))]
  · change ratio ^ (denominator * index) * first ≤ ratio ^ (denominator * index)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hfirst_bounds.2 (pow_nonneg hratio.le _)

/-- An exact strict logarithmic link yields infinitely many actual rational
curve/Cantor intersections. Only the standalone strict-link obligation remains
as a premise; perturbation, Gap Lemma intersection and shell witnesses are proved. -/
theorem coarse_rational_infinite_intersection_of_strict_link {ratio exponent : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2) (hexponent : 1 < exponent)
    {numerator denominator : ℕ} (hnumerator : 0 < numerator) (hdenominator : 0 < denominator)
    (hphase : exponent * denominator = numerator) (hlink : CoarseStrictLogLink ratio exponent) :
    (intersection exponent ratio).Infinite := by
  have hratio : 0 < ratio := by linarith
  have hless : ratio < 1 := by linarith
  obtain ⟨shift, hintersections⟩ := coarse_actual_log_intersections_of_strict_link hlower hupper hexponent hlink
  let scales : ℕ → ℝ := fun index => ratio ^ (shift : ℝ) * ratio ^ (numerator * index)
  have hscales_positive : ∀ index, 0 < scales index := by
    intro index
    exact mul_pos (Real.rpow_pos_of_pos hratio _) (pow_pos hratio _)
  have hpower_less : ratio ^ numerator < 1 := pow_lt_one₀ hratio.le hless hnumerator.ne'
  have hscales_zero : Tendsto scales atTop (𝓝 0) := by
    have hlimit := (tendsto_pow_atTop_nhds_zero_of_lt_one (pow_nonneg hratio.le numerator) hpower_less).const_mul
      (ratio ^ (shift : ℝ))
    simpa only [scales, pow_mul, mul_zero] using hlimit
  have hactual := hintersections scales hscales_positive hscales_zero
  obtain ⟨depthBound, hdepthBound⟩ := exists_nat_gt (-shift)
  have hdepth : ∀ᶠ index : ℕ in atTop, 0 ≤ shift + (numerator * index : ℕ) := by
    filter_upwards [eventually_ge_atTop depthBound] with index hindex
    have hlarge : index ≤ numerator * index := by nlinarith
    omega
  obtain ⟨offset, hoffset⟩ := eventually_atTop.mp (hactual.and hdepth)
  apply infinite_intersection_of_outer_shell_witnesses hratio hupper hdenominator
    (offset := offset)
  intro index
  have hboth := hoffset (index + offset) (by omega)
  obtain ⟨first, hfirst, second, hsecond, hdrop, hequation⟩ := hboth.1
  exact coarse_actual_rational_shell_point hratio hless hexponent hphase shift hboth.2
    hfirst hsecond hdrop hequation

end LambdaCantor.Last
