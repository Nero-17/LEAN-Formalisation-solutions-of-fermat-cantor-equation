import LambdaCantor.First.RootsKernelLimit
import LambdaCantor.First.RootsMeasures
import Mathlib.Topology.ContinuousOn

noncomputable section
open Filter Topology MeasureTheory
namespace LambdaCantor.First.Roots

/-- Choose one actual point in each finite cylinder meeting the given set.
The default outside those cylinders retains the prescribed finite word. -/
def prefixRepresentative (selected : Set (ℕ → Bool × Bool)) (depth : ℕ)
    (word : Fin depth → Bool × Bool) : ℕ → Bool × Bool := by
  classical
  exact if witness : ∃ digits ∈ selected, ∀ index : Fin depth, digits index = word index then
    Classical.choose witness
  else fun index => if before : index < depth then word ⟨index, before⟩ else (false, false)

theorem prefixRepresentative_matches (selected : Set (ℕ → Bool × Bool)) (depth : ℕ)
    (word : Fin depth → Bool × Bool) (index : Fin depth) :
    prefixRepresentative selected depth word index = word index := by
  classical
  unfold prefixRepresentative
  split_ifs with witness
  · exact (Classical.choose_spec witness).2 index
  · simp

theorem prefixRepresentative_mem (selected : Set (ℕ → Bool × Bool)) (depth : ℕ)
    (word : Fin depth → Bool × Bool)
    (witness : ∃ digits ∈ selected, ∀ index : Fin depth, digits index = word index) :
    prefixRepresentative selected depth word ∈ selected := by
  classical
  simp only [prefixRepresentative, dif_pos witness]
  exact (Classical.choose_spec witness).1

/-- The actual kernel chosen on each finite cylinder, evaluated at its full tail. -/
def selectedRootKernel {exponent : ℝ} (data : RootFibreData exponent)
    (selected : Set (ℕ → Bool × Bool)) (depth : ℕ) (digits : ℕ → Bool × Bool) : ℝ :=
  completeRootKernel data
    (prefixRepresentative selected depth (fun index : Fin depth => digits index)) depth
    (fun index => digits (index + depth))

theorem selectedRootKernel_eq {exponent : ℝ} (data : RootFibreData exponent)
    (selected : Set (ℕ → Bool × Bool)) (depth : ℕ) (digits : ℕ → Bool × Bool) :
    selectedRootKernel data selected depth digits = rootKernelValue data
      (prefixRepresentative selected depth (fun index : Fin depth => digits index)) digits depth := by
  apply rootKernelValue_depends_only_on_tail
  intro index
  simp only [pairedCylinderDigits_after]

theorem continuous_selectedRootKernel {exponent : ℝ} (data : RootFibreData exponent)
    (selected : Set (ℕ → Bool × Bool)) (depth : ℕ) :
    Continuous (selectedRootKernel data selected depth) := by
  have kernel_continuous : Continuous (fun pair : (Fin depth → Bool × Bool) × (ℕ → Bool × Bool) =>
      completeRootKernel data (prefixRepresentative selected depth pair.1) depth pair.2) :=
    continuous_prod_of_discrete_left.mpr (fun word =>
      continuous_completeRootKernel data (prefixRepresentative selected depth word) depth)
  have prefix_continuous : Continuous (fun digits : ℕ → Bool × Bool =>
      fun index : Fin depth => digits index) :=
    continuous_pi (fun index : Fin depth => continuous_apply (index : ℕ))
  have tail_continuous : Continuous (fun digits : ℕ → Bool × Bool =>
      fun index : ℕ => digits (index + depth)) :=
    continuous_pi (fun index : ℕ => continuous_apply (index + depth))
  change Continuous ((fun pair : (Fin depth → Bool × Bool) × (ℕ → Bool × Bool) =>
    completeRootKernel data (prefixRepresentative selected depth pair.1) depth pair.2) ∘
      (fun digits : ℕ → Bool × Bool =>
        ((fun index : Fin depth => digits index), fun index : ℕ => digits (index + depth))))
  exact kernel_continuous.comp (prefix_continuous.prodMk tail_continuous)

theorem selectedRootKernel_tendsto {exponent : ℝ} (data : RootFibreData exponent)
    (selected : Set (ℕ → Bool × Bool)) (digits : ℕ → Bool × Bool) :
    Tendsto (fun depth => selectedRootKernel data selected depth digits) atTop (𝓝 (data.root digits)) := by
  simp_rw [selectedRootKernel_eq]
  apply rootFibreData_kernel_tendsto
  intro depth other index before
  exact prefixRepresentative_matches selected depth (fun index : Fin depth => other index) ⟨index, before⟩

/-- Bounded continuous tests of the actual finite-prefix kernels converge to
those of the actual root map, including after restriction to any source set. -/
theorem selectedRootKernel_integral_tendsto {exponent : ℝ} (data : RootFibreData exponent)
    (selected source : Set (ℕ → Bool × Bool)) (test : ℝ → ℝ)
    (test_continuous : Continuous test) (bound : ℝ) (test_bounded : ∀ value, ‖test value‖ ≤ bound) :
    Tendsto (fun depth => ∫ digits, test (selectedRootKernel data selected depth digits)
      ∂pairedAddressMeasure.restrict source) atTop
      (𝓝 (∫ digits, test (data.root digits) ∂pairedAddressMeasure.restrict source)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => bound)
  · intro depth
    exact (test_continuous.comp (continuous_selectedRootKernel data selected depth)).measurable.aestronglyMeasurable
  · exact integrable_const bound
  · intro depth
    exact Filter.Eventually.of_forall (fun digits => test_bounded _)
  · exact Filter.Eventually.of_forall (fun digits =>
      test_continuous.continuousAt.tendsto.comp (selectedRootKernel_tendsto data selected digits))

end LambdaCantor.First.Roots
