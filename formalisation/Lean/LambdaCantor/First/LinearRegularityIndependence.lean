import LambdaCantor.First.RootsMeasures
import LambdaCantor.First.LinearRegularityDigits
import Mathlib.Probability.Independence.InfinitePi

noncomputable section
open MeasureTheory ProbabilityTheory
namespace LambdaCantor.First.LinearRegularity

/-- Actual projected law on the fair paired-address probability space. -/
def pairedProjection (ratio slope : ℝ) (digits : ℕ → Bool × Bool) : ℝ :=
  slope * address ratio (fun index => (digits index).1) +
    address ratio (fun index => (digits index).2)

theorem measurable_pairedProjection {ratio : ℝ} (hpos : 0 ≤ ratio) (hlt : ratio < 1) (slope : ℝ) :
    Measurable (pairedProjection ratio slope) := by
  unfold pairedProjection
  have haddress := (continuous_address hpos hlt).measurable
  exact ((haddress.comp (by fun_prop)).const_mul slope).add (haddress.comp (by fun_prop))

/-- Independence of the full (possibly infinite) restrictions to disjoint
coordinate sets, under the actual fair paired-address product probability. -/
theorem paired_restrictions_independent (left right : Set ℕ) (hdisjoint : Disjoint left right) :
    IndepFun (fun digits : ℕ → Bool × Bool => fun index : left => digits index)
      (fun digits : ℕ → Bool × Bool => fun index : right => digits index) Roots.pairedAddressMeasure := by
  have hindependent : iIndepFun (fun index (digits : ℕ → Bool × Bool) => digits index)
      Roots.pairedAddressMeasure := by
    exact iIndepFun_infinitePi (X := fun (_ : ℕ) (pair : Bool × Bool) => pair) (by fun_prop)
  have hsup := indep_iSup_of_disjoint
    (fun index : ℕ => (measurable_pi_apply index : Measurable
      (fun digits : ℕ → Bool × Bool => digits index)).comap_le) hindependent hdisjoint
  change Indep (MeasurableSpace.comap (fun digits : ℕ → Bool × Bool => fun index : left => digits index)
      MeasurableSpace.pi)
    (MeasurableSpace.comap (fun digits : ℕ → Bool × Bool => fun index : right => digits index)
      MeasurableSpace.pi) Roots.pairedAddressMeasure
  simpa only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, iSup_subtype] using hsup

/-- Extension of a restricted paired address by the zero symbol. -/
def extendPairedDigits (positions : Set ℕ) (digits : positions → Bool × Bool) (index : ℕ) : Bool × Bool :=
  by
  classical
  exact if hindex : index ∈ positions then digits ⟨index, hindex⟩ else (false, false)

theorem measurable_extendPairedDigits (positions : Set ℕ) : Measurable (extendPairedDigits positions) := by
  classical
  apply measurable_pi_lambda
  intro index
  unfold extendPairedDigits
  split_ifs <;> fun_prop

/-- The sparse and dense projected factors are independent actual random
variables, not merely a formal splitting of their address series. -/
theorem sparse_dense_projections_independent {ratio : ℝ} (hpos : 0 ≤ ratio) (hlt : ratio < 1)
    (slope : ℝ) (blockLength : ℕ) :
    IndepFun
      (fun digits : ℕ → Bool × Bool =>
        slope * address ratio (sparseDigits blockLength (fun index => (digits index).1)) +
          address ratio (sparseDigits blockLength (fun index => (digits index).2)))
      (fun digits : ℕ → Bool × Bool =>
        slope * address ratio (denseDigits blockLength (fun index => (digits index).1)) +
          address ratio (denseDigits blockLength (fun index => (digits index).2)))
      Roots.pairedAddressMeasure := by
  classical
  have hrestriction := paired_restrictions_independent {index | index % blockLength = 0}
    {index | index % blockLength ≠ 0} (by simp [Set.disjoint_left])
  have hcomposed := hrestriction.comp
    ((measurable_pairedProjection hpos hlt slope).comp
      (measurable_extendPairedDigits {index | index % blockLength = 0}))
    ((measurable_pairedProjection hpos hlt slope).comp
      (measurable_extendPairedDigits {index | index % blockLength ≠ 0}))
  have hsparse (digits : ℕ → Bool × Bool) :
      pairedProjection ratio slope
        (extendPairedDigits {index | index % blockLength = 0} (fun index => digits index)) =
      slope * address ratio (sparseDigits blockLength (fun index => (digits index).1)) +
        address ratio (sparseDigits blockLength (fun index => (digits index).2)) := by
    unfold pairedProjection
    have hleft : (fun index =>
        (extendPairedDigits {index | index % blockLength = 0} (fun index => digits index) index).1) =
        sparseDigits blockLength (fun index => (digits index).1) := by
      funext index
      by_cases hindex : index % blockLength = 0 <;> simp [extendPairedDigits, sparseDigits, hindex]
    have hright : (fun index =>
        (extendPairedDigits {index | index % blockLength = 0} (fun index => digits index) index).2) =
        sparseDigits blockLength (fun index => (digits index).2) := by
      funext index
      by_cases hindex : index % blockLength = 0 <;> simp [extendPairedDigits, sparseDigits, hindex]
    rw [hleft, hright]
  have hdense (digits : ℕ → Bool × Bool) :
      pairedProjection ratio slope
        (extendPairedDigits {index | index % blockLength ≠ 0} (fun index => digits index)) =
      slope * address ratio (denseDigits blockLength (fun index => (digits index).1)) +
        address ratio (denseDigits blockLength (fun index => (digits index).2)) := by
    unfold pairedProjection
    have hleft : (fun index =>
        (extendPairedDigits {index | index % blockLength ≠ 0} (fun index => digits index) index).1) =
        denseDigits blockLength (fun index => (digits index).1) := by
      funext index
      by_cases hindex : index % blockLength = 0 <;> simp [extendPairedDigits, denseDigits, hindex]
    have hright : (fun index =>
        (extendPairedDigits {index | index % blockLength ≠ 0} (fun index => digits index) index).2) =
        denseDigits blockLength (fun index => (digits index).2) := by
      funext index
      by_cases hindex : index % blockLength = 0 <;> simp [extendPairedDigits, denseDigits, hindex]
    rw [hleft, hright]
  simpa only [Function.comp_def, hsparse, hdense] using hcomposed

end LambdaCantor.First.LinearRegularity

