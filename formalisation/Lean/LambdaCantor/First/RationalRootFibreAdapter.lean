import LambdaCantor.First.RealNormalizationAdapter
import LambdaCantor.First.RationalLattice
import LambdaCantor.First.RationalDenominatorComparison

noncomputable section
namespace LambdaCantor.First.Roots

/-- A reduced rational exponent supplies actual full-tail root-fibre data
inside every band around each positive lattice comparison root. -/
theorem rational_rootFibreData {numerator denominator : ℕ}
    (hnumerator : 0 < numerator) (hdenominator : 0 < denominator)
    (hcoprime : numerator.Coprime denominator)
    {phase lower target upper : ℝ}
    (hexponent : 1 < (numerator : ℝ) / denominator)
    (hphase : 0 < phase)
    (hlattice : ∃ phaseNumerator : ℤ, (denominator : ℝ) * phase = phaseNumerator)
    (hzero : comparison ((numerator : ℝ) / denominator) phase target = 0)
    (hlower : (1 / 4 : ℝ) < lower) (hleft : lower < target)
    (hright : target < upper) (hupper : upper < 1 / 2) :
    ∃ data : RootFibreData ((numerator : ℝ) / denominator),
      data.lower = lower ∧ data.upper = upper := by
  obtain ⟨leftDepth, rightDepth, hleftDepth, hrightDepth, hphases⟩ :=
    rational_phase_sequences numerator denominator hnumerator hdenominator hcoprime phase hlattice
  have hphaseLimit : Filter.Tendsto
      (fun index => (rightDepth index : ℝ) -
        ((numerator : ℝ) / denominator) * (leftDepth index : ℝ))
      Filter.atTop (nhds phase) := by
    simpa only [hphases] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => phase) Filter.atTop (nhds phase))
  have hroots := full_tail_roots_of_phase_sequences hexponent
    (lt_trans (by norm_num) hlower) hleft hright (lt_trans hupper (by norm_num))
    hphase hzero leftDepth rightDepth hrightDepth hphaseLimit
  obtain ⟨index, hindex, hpadding, hrightPositive⟩ :=
    (hroots.and ((Filter.eventually_ge_atTop (1 : ℕ)).and
      (hrightDepth.eventually (Filter.eventually_ge_atTop 1)))).exists
  exact firstRoot_rootFibreData_of_roots hexponent hlower hupper (hleft.trans hright)
    (leftDepth index) (rightDepth index) index hpadding hrightPositive hindex

/-- The denominator construction has an actual interior comparison root
with its exact quantitative displacement, and actual geometric data in
every sufficiently small surrounding parameter band. -/
theorem rational_denominator_rootFibreData (numerator denominator : ℕ)
    (hnumerator : 0 < numerator) (hdenominator : 0 < denominator)
    (hcoprime : numerator.Coprime denominator)
    (hexponent : 2 ≤ (numerator : ℝ) / denominator) :
    ∃ target : ℝ, target ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∧
      target - 1 / 4 ≤ (3 / 2 : ℝ) ^ ((numerator : ℝ) / denominator) * Real.log 4 /
        (2 * ((numerator : ℝ) / denominator) * denominator) ∧
      ∀ lower upper : ℝ, (1 / 4 : ℝ) < lower → lower < target →
        target < upper → upper < 1 / 2 →
        ∃ data : RootFibreData ((numerator : ℝ) / denominator),
          data.lower = lower ∧ data.upper = upper := by
  let exponent : ℝ := (numerator : ℝ) / denominator
  let phase : ℝ := ((⌊(denominator : ℝ) *
    ((exponent * Real.log (4 / 3) + Real.log exponent) / Real.log 4)⌋ : ℤ) + 1) /
      (denominator : ℝ)
  have hstep := next_lattice_point
    ((exponent * Real.log (4 / 3) + Real.log exponent) / Real.log 4)
    denominator hdenominator
  have hphaseLower : (exponent * Real.log (4 / 3) + Real.log exponent) / Real.log 4 < phase := by
    dsimp [phase]
    simpa only [Int.cast_add, Int.cast_one] using sub_pos.mp hstep.1
  have hdenominatorReal : (1 : ℝ) ≤ denominator := by
    exact_mod_cast (Nat.succ_le_of_lt hdenominator)
  have hreciprocal : 1 / (denominator : ℝ) ≤ 1 :=
    (div_le_one (by positivity : (0 : ℝ) < denominator)).mpr hdenominatorReal
  obtain ⟨target, htarget, _⟩ := exists_unique_rationalComparison_root hexponent hphaseLower
    (by dsimp [phase]; linarith [hstep.2])
  have hphase : 0 < phase := (comparison_balance_phase_pos hexponent).trans hphaseLower
  refine ⟨target, htarget.1, ?_, ?_⟩
  · exact rationalComparison_root_denominator_bound denominator hexponent hdenominator hphase.le
      (by dsimp [phase]; simpa only [Int.cast_add, Int.cast_one] using hstep.2)
      ⟨htarget.1.1.le, htarget.1.2.le⟩ htarget.2
  · intro lower upper hlower hleft hright hupper
    apply rational_rootFibreData hnumerator hdenominator hcoprime
      (by linarith) hphase _ htarget.2 hlower hleft hright hupper
    refine ⟨⌊(denominator : ℝ) *
      ((exponent * Real.log (4 / 3) + Real.log exponent) / Real.log 4)⌋ + 1, ?_⟩
    dsimp [phase]
    field_simp
    simp only [Int.cast_add, Int.cast_one]

end LambdaCantor.First.Roots
