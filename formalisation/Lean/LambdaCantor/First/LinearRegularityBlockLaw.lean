import LambdaCantor.First.RootsMeasures
import LambdaCantor.First.LinearRegularityBlocks
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace LambdaCantor.First.LinearRegularity

/-- The actual retained symbols, grouped into consecutive dense blocks. -/
def denseBlockCoding (blockLength : ℕ) (digits : ℕ → Bool × Bool)
    (block : ℕ) (offset : Fin (blockLength - 1)) : Bool × Bool :=
  digits (blockLength * block + offset.val + 1)

theorem measurable_denseBlockCoding (blockLength : ℕ) :
    Measurable (denseBlockCoding blockLength) := by
  unfold denseBlockCoding
  fun_prop

/-- Distinct retained positions in distinct blocks never use the same digit. -/
theorem denseBlockIndex_injective (blockLength : ℕ) :
    Function.Injective (fun position : ℕ × Fin (blockLength - 1) =>
      blockLength * position.1 + position.2.val + 1) := by
  intro left right heq
  have hleft : left.2.val < blockLength := lt_of_lt_of_le left.2.isLt (Nat.sub_le _ _)
  have hright : right.2.val < blockLength := lt_of_lt_of_le right.2.isLt (Nat.sub_le _ _)
  have hblock : left.1 = right.1 := by
    rcases lt_trichotomy left.1 right.1 with hlt | hequal | hgt
    · have hmul := Nat.mul_le_mul_left blockLength (Nat.succ_le_of_lt hlt)
      nlinarith
    · exact hequal
    · have hmul := Nat.mul_le_mul_left blockLength (Nat.succ_le_of_lt hgt)
      nlinarith
  apply Prod.ext hblock
  apply Fin.ext
  simp only [hblock] at heq
  omega

/-- The finite product of fair paired digits is exactly the uniform block law. -/
theorem denseBlock_uniform (blockLength : ℕ) :
    Measure.infinitePi (fun _ : Fin (blockLength - 1) =>
      (PMF.uniformOfFintype (Bool × Bool)).toMeasure) =
    (PMF.uniformOfFintype (DenseBlock blockLength)).toMeasure := by
  apply Measure.ext_of_singleton
  intro word
  rw [Measure.infinitePi_singleton_of_fintype]
  simp [PMF.toMeasure_apply_singleton, measurableSet_singleton,
    PMF.uniformOfFintype_apply, Fintype.card_prod, denseBlock_card,
    ENNReal.inv_pow]

/-- Exact IID law of the retained dense blocks under the original paired
address probability. No independence or uniformity is postulated. -/
theorem denseBlockCoding_law (blockLength : ℕ) :
    Roots.pairedAddressMeasure.map (denseBlockCoding blockLength) =
    Measure.infinitePi (fun _ : ℕ =>
      (PMF.uniformOfFintype (DenseBlock blockLength)).toMeasure) := by
  have hsample := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => (PMF.uniformOfFintype (Bool × Bool)).toMeasure)
    (denseBlockIndex_injective blockLength)
  have hcurry := Measure.infinitePi_map_curry
    (fun (_ : ℕ) (_ : Fin (blockLength - 1)) =>
      (PMF.uniformOfFintype (Bool × Bool)).toMeasure)
  calc
    Roots.pairedAddressMeasure.map (denseBlockCoding blockLength) =
        (Roots.pairedAddressMeasure.map
          (fun digits (position : ℕ × Fin (blockLength - 1)) =>
            digits (blockLength * position.1 + position.2.val + 1))).map
          (MeasurableEquiv.curry ℕ (Fin (blockLength - 1)) (Bool × Bool)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (Measure.infinitePi (fun _ : ℕ × Fin (blockLength - 1) =>
        (PMF.uniformOfFintype (Bool × Bool)).toMeasure)).map
          (MeasurableEquiv.curry ℕ (Fin (blockLength - 1)) (Bool × Bool)) := by
      rw [show Roots.pairedAddressMeasure.map
          (fun digits (position : ℕ × Fin (blockLength - 1)) =>
            digits (blockLength * position.1 + position.2.val + 1)) = _ from hsample]
    _ = Measure.infinitePi (fun _ : ℕ =>
        Measure.infinitePi (fun _ : Fin (blockLength - 1) =>
          (PMF.uniformOfFintype (Bool × Bool)).toMeasure)) := hcurry
    _ = _ := by simp_rw [denseBlock_uniform]

end LambdaCantor.First.LinearRegularity

