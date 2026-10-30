import LambdaCantor.First.Library.DenseSubgroup
import LambdaCantor.First.Library.SubmonoidClosure
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.Instances.AddCircle.Real

noncomputable section
open Set
namespace LambdaCantor

/-- Natural irrational rotations are dense, including the direction needed
for the phases m - n*k in the source construction. -/
theorem dense_negative_irrational_rotation {exponent : ℝ}
    (hirrational : Irrational exponent) :
    DenseRange (fun depth : ℕ => depth • ((-exponent : ℝ) : AddCircle (1 : ℝ))) := by
  letI : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  apply denseRange_zsmul_iff_nsmul.mp
  exact AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using hirrational.neg)



/-- Arbitrarily deep integer phases approximate any prescribed real phase.
This is the irrational-rotation step in the full-tail cylinder construction. -/
theorem irrational_phase_approximation {exponent : ℝ}
    (hirrational : Irrational exponent) (phase tolerance : ℝ)
    (htolerance : 0 < tolerance) (minimumDepth : ℕ) :
    ∃ depth : ℕ, minimumDepth ≤ depth ∧ ∃ numerator : ℤ,
      |(numerator : ℝ) - exponent * depth - phase| < tolerance := by
  have hsurjective : Function.Surjective
      (fun point : AddCircle (1 : ℝ) =>
        point + minimumDepth • ((-exponent : ℝ) : AddCircle (1 : ℝ))) := by
    intro point
    exact ⟨point - minimumDepth • ((-exponent : ℝ) : AddCircle (1 : ℝ)),
      sub_add_cancel _ _⟩
  have hdense := hsurjective.denseRange.comp
    (dense_negative_irrational_rotation hirrational)
    (continuous_id.add continuous_const)
  have hopen : IsOpen (((↑) : ℝ → AddCircle (1 : ℝ)) ''
      Set.Ioo (phase - tolerance) (phase + tolerance)) :=
    QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hnonempty : (((↑) : ℝ → AddCircle (1 : ℝ)) ''
      Set.Ioo (phase - tolerance) (phase + tolerance)).Nonempty :=
    ⟨(phase : AddCircle (1 : ℝ)), phase, ⟨by linarith, by linarith⟩, rfl⟩
  obtain ⟨extraDepth, representative, hrepresentative, heq⟩ :=
    hdense.exists_mem_open hopen hnonempty
  have hzero : ((representative + (extraDepth + minimumDepth : ℕ) * exponent : ℝ) :
      AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_add, heq]
    change extraDepth • ((-exponent : ℝ) : AddCircle (1 : ℝ)) +
      minimumDepth • ((-exponent : ℝ) : AddCircle (1 : ℝ)) +
      (((extraDepth + minimumDepth : ℕ) : ℝ) * exponent : ℝ) = 0
    rw [← add_nsmul]
    simp [← AddCircle.coe_nsmul (1 : ℝ), nsmul_eq_mul]
  obtain ⟨numerator, hnumerator⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  refine ⟨extraDepth + minimumDepth, Nat.le_add_left _ _, numerator, ?_⟩
  have hidentity : (numerator : ℝ) - exponent * (extraDepth + minimumDepth : ℕ) =
      representative := by
    simp only [zsmul_eq_mul, mul_one] at hnumerator
    nlinarith [hnumerator]
  rw [hidentity, abs_lt]
  constructor <;> linarith [hrepresentative.1, hrepresentative.2]



/-- The approximation can be realized by two arbitrarily large natural numbers,
as required by the two actual cylinder prefixes. -/
theorem irrational_positive_phase_approximation {exponent phase : ℝ}
    (hirrational : Irrational exponent) (hexponent : 1 < exponent)
    (hphase : 0 < phase) (tolerance : ℝ) (htolerance : 0 < tolerance)
    (minimumDepth : ℕ) :
    ∃ depth numerator : ℕ, minimumDepth < depth ∧ minimumDepth < numerator ∧
      |(numerator : ℝ) - exponent * depth - phase| < tolerance := by
  obtain ⟨depth, hdepth, numerator, happrox⟩ := irrational_phase_approximation
    hirrational phase (min tolerance (phase / 2))
    (lt_min htolerance (by linarith)) (minimumDepth + 1)
  have hdepth_pos : (0 : ℝ) < depth := by
    have : 0 < depth := lt_of_lt_of_le (Nat.succ_pos _) hdepth
    exact_mod_cast this
  have hlower := (abs_lt.mp happrox).1
  have hsmall := min_le_right tolerance (phase / 2)
  have hnum_gt : (depth : ℝ) < numerator := by nlinarith
  have hnum_nonneg : 0 ≤ numerator := by
    exact_mod_cast (le_of_lt (lt_trans hdepth_pos hnum_gt))
  have hnum_cast : (numerator.toNat : ℝ) = numerator := by
    exact_mod_cast Int.toNat_of_nonneg hnum_nonneg
  refine ⟨depth, numerator.toNat, by omega, ?_, ?_⟩
  · have : (minimumDepth : ℝ) < numerator.toNat := by
      rw [hnum_cast]
      have : (minimumDepth : ℝ) < depth := by exact_mod_cast (show minimumDepth < depth by omega)
      linarith
    exact_mod_cast this
  · rw [hnum_cast]
    exact lt_of_lt_of_le happrox (min_le_left _ _)





/-- The exact sequence formulation used in Theorem irrational-parameters. -/
theorem irrational_positive_phase_sequences {exponent phase : ℝ}
    (hirrational : Irrational exponent) (hexponent : 1 < exponent)
    (hphase : 0 < phase) :
    ∃ depth numerator : ℕ → ℕ,
      Filter.Tendsto depth Filter.atTop Filter.atTop ∧
      Filter.Tendsto numerator Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun index => (numerator index : ℝ) - exponent * depth index)
        Filter.atTop (nhds phase) := by
  have happrox : ∀ index : ℕ, ∃ depth numerator : ℕ,
      index < depth ∧ index < numerator ∧
      |(numerator : ℝ) - exponent * depth - phase| < 1 / ((index : ℝ) + 1) := by
    intro index
    apply irrational_positive_phase_approximation hirrational hexponent hphase
    positivity
  choose depth numerator hdepth hnumerator herror using happrox
  refine ⟨depth, numerator, ?_, ?_, ?_⟩
  · exact Filter.tendsto_atTop_mono (fun index => (hdepth index).le) Filter.tendsto_id
  · exact Filter.tendsto_atTop_mono (fun index => (hnumerator index).le) Filter.tendsto_id
  · apply (tendsto_iff_norm_sub_tendsto_zero (f := fun index => (numerator index : ℝ) - exponent * depth index) (b := phase)).mpr
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun index => by simpa only [Real.norm_eq_abs] using (herror index).le)
      tendsto_one_div_add_atTop_nhds_zero_nat

end LambdaCantor



