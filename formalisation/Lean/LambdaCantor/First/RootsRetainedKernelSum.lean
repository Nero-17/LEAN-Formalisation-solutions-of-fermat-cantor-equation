import LambdaCantor.First.RootsPrefixObservable
import LambdaCantor.First.RootsRefinementWords

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

open scoped Classical in
/-- Surviving parent kernels and the next child approximation are indexed by
the same child words, with exactly the same original Bernoulli weights. -/
theorem retainedRootKernel_law_eq_sum {exponent : ℝ} (data : RootFibreData exponent)
    (selected : Set (ℕ → Bool × Bool)) (depth : ℕ) :
    (pairedAddressMeasure.restrict (prefixNeighborhood selected (depth + 1))).map
      (selectedRootKernel data selected depth) =
      ∑ word : Fin (depth + 1) → Bool × Bool,
        if ∃ representative ∈ selected, ∀ index : Fin (depth + 1), representative index = word index then
          ((4 : ℝ≥0∞)⁻¹ ^ (depth + 1)) • pairedAddressMeasure.map
            (fun tail => completeRootKernel data
              (prefixRepresentative selected depth (parentWord word)) depth
              (prependPairedDigit (word (Fin.last depth)) tail))
        else 0 := by
  let combine : (Fin (depth + 1) → Bool × Bool) × (ℕ → Bool × Bool) → ℝ :=
    fun pair => completeRootKernel data
      (prefixRepresentative selected depth (parentWord pair.1)) depth
      (prependPairedDigit (pair.1 (Fin.last depth)) pair.2)
  have combine_measurable : Measurable combine := by
    apply Continuous.measurable
    apply continuous_prod_of_discrete_left.mpr
    intro word
    change Continuous (fun tail : ℕ → Bool × Bool =>
      completeRootKernel data (prefixRepresentative selected depth (parentWord word)) depth
        (prependPairedDigit (word (Fin.last depth)) tail))
    have prepend_continuous : Continuous (fun tail : ℕ → Bool × Bool =>
        prependPairedDigit (word (Fin.last depth)) tail) := by
      let pairWithDigit : (ℕ → Bool × Bool) → (Bool × Bool) × (ℕ → Bool × Bool) :=
        fun tail => (word (Fin.last depth), tail)
      let prepend : (Bool × Bool) × (ℕ → Bool × Bool) → (ℕ → Bool × Bool) :=
        fun point => prependPairedDigit point.1 point.2
      have pair_continuous : Continuous pairWithDigit := continuous_const.prodMk continuous_id
      have prepend_joint_continuous : Continuous prepend := continuous_prependPairedDigit
      have composed : Continuous (prepend ∘ pairWithDigit) :=
        Continuous.comp (f := pairWithDigit) (g := prepend)
          prepend_joint_continuous pair_continuous
      have identification : prepend ∘ pairWithDigit =
          (fun tail : ℕ → Bool × Bool => prependPairedDigit (word (Fin.last depth)) tail) := by
        funext tail
        rfl
      rw [← identification]
      exact composed
    exact (continuous_completeRootKernel data
      (prefixRepresentative selected depth (parentWord word)) depth).comp prepend_continuous
  have pointwise : selectedRootKernel data selected depth =
      fun digits => combine ((fun index : Fin (depth + 1) => digits index),
        fun index => digits (index + (depth + 1))) := by
    funext digits
    unfold selectedRootKernel combine
    congr 1
    funext index
    simp only [prependPairedDigit]
    split_ifs with zero
    · subst index
      simp
    · congr 1
      omega
  rw [pointwise]
  exact prefixRestrictedLaw_eq_sum selected (depth + 1) combine combine_measurable

end LambdaCantor.First.Roots
