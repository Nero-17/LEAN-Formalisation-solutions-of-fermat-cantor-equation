import LambdaCantor.First.RootsKernelDensity
import LambdaCantor.First.RootsKernelSum
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

theorem hasL2Density_zero : LinearRegularity.HasL2Density (0 : Measure ℝ) := by
  refine ⟨0, fun _ => le_rfl, measurable_const, integrable_zero ℝ ℝ volume, MemLp.zero, ?_⟩
  simp

theorem hasL2Density_add {first second : Measure ℝ}
    (first_density : LinearRegularity.HasL2Density first)
    (second_density : LinearRegularity.HasL2Density second) :
    LinearRegularity.HasL2Density (first + second) := by
  obtain ⟨firstFunction, first_nonnegative, first_measurable, first_integrable, first_square, first_law⟩ := first_density
  obtain ⟨secondFunction, second_nonnegative, second_measurable, second_integrable, second_square, second_law⟩ := second_density
  refine ⟨fun point => firstFunction point + secondFunction point,
    fun point => add_nonneg (first_nonnegative point) (second_nonnegative point),
    first_measurable.add second_measurable, first_integrable.add second_integrable,
    first_square.add second_square, ?_⟩
  rw [first_law, second_law, ← withDensity_add_left first_measurable.ennreal_ofReal]
  congr 1
  funext point
  exact (ENNReal.ofReal_add (first_nonnegative point) (second_nonnegative point)).symm

theorem hasL2Density_smul {measure : Measure ℝ} (density_exists : LinearRegularity.HasL2Density measure)
    (weight : ℝ≥0∞) (finite_weight : weight ≠ ∞) : LinearRegularity.HasL2Density (weight • measure) := by
  obtain ⟨density, nonnegative, measurable, integrable, square, law⟩ := density_exists
  refine ⟨fun point => weight.toReal * density point,
    fun point => mul_nonneg ENNReal.toReal_nonneg (nonnegative point),
    measurable_const.mul measurable, integrable.const_mul _, square.const_mul _, ?_⟩
  rw [law, ← withDensity_smul _ measurable.ennreal_ofReal]
  congr 1
  funext point
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal finite_weight]

theorem hasL2Density_finset_sum {Index : Type*} (indices : Finset Index) (measures : Index → Measure ℝ)
    (density_exists : ∀ index ∈ indices, LinearRegularity.HasL2Density (measures index)) :
    LinearRegularity.HasL2Density (∑ index ∈ indices, measures index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using hasL2Density_zero
  | @insert index indices not_member induction_hypothesis =>
    rw [Finset.sum_insert not_member]
    exact hasL2Density_add (density_exists index (Finset.mem_insert_self _ _))
      (induction_hypothesis (fun other member => density_exists other (Finset.mem_insert_of_mem member)))

/-- Every finite approximation has an actual L1/L2 density once the actual
projected state laws on the chosen source set have those densities. -/
theorem selectedRootKernel_law_hasL2Density {exponent : ℝ} (data : RootFibreData exponent)
    (selected : Set (ℕ → Bool × Bool)) (depth : ℕ)
    (projected_densities : ∀ representative ∈ selected, LinearRegularity.HasL2Density
      (pairedAddressMeasure.map (projectedRootModel (rootFibreState data representative)))) :
    LinearRegularity.HasL2Density
      ((pairedAddressMeasure.restrict (prefixNeighborhood selected depth)).map
        (selectedRootKernel data selected depth)) := by
  classical
  rw [selectedRootKernel_law_eq_sum]
  apply hasL2Density_finset_sum
  intro word _
  split_ifs with witness
  · apply hasL2Density_smul
    · exact completeRootKernelLaw_hasL2Density data _ depth
        (projected_densities _ (prefixRepresentative_mem selected depth word witness))
    · finiteness
  · exact hasL2Density_zero

end LambdaCantor.First.Roots
