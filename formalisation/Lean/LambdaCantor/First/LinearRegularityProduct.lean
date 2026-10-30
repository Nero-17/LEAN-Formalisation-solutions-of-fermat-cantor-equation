import Mathlib.Tactic.Linarith
import LambdaCantor.First.LinearRegularityExceptions

/-!
# Standard external Hausdorff product bound and its internal applications

Kenneth Falconer, Fractal Geometry: Mathematical Foundations and Applications,
second edition (2003), Product formula 7.3, equation (7.7), printed page 102.
Publisher: https://doi.org/10.1002/0470013850.ch7
Primary book text read at:
https://www.muslimuniversity.edu.af/uploads/library/Fractal.Geometry.Mathematical.Foundations.and.Applications.Second.Edition.eBook-EEn_957.pdf
PDF page 128 (one-based). The statement applies to arbitrary sets and bounds
Hausdorff dimension of a Cartesian product by the Hausdorff dimension of the
first factor plus the upper box dimension of the second. Here the second
factor is a compact real interval, whose upper box dimension is at most one.
The standard max metric on the Lean real product is bi-Lipschitz equivalent
to the Euclidean product metric, so the Hausdorff dimensions coincide.
-/

noncomputable section
namespace LambdaCantor.First.LinearRegularity

/-- Established standard external product-dimension theorem, specialized to
a real set and a compact real interval. This is independent of the manuscript. -/
axiom falconer2003_product73_interval (set : Set ℝ) (lower upper : ℝ)
    (hordered : lower ≤ upper) :
    dimH (set ×ˢ Set.Icc lower upper) ≤ dimH set + 1

/-- A zero-dimensional contraction exception remains at most one-dimensional
when every real slope is included. The unbounded extension is proved here. -/
theorem dimH_zero_exception_times_real (exceptional : Set ℝ) (hexceptional : dimH exceptional = 0) :
    dimH (exceptional ×ˢ (Set.univ : Set ℝ)) ≤ 1 := by
  have hcover : exceptional ×ˢ (Set.univ : Set ℝ) ⊆
      ⋃ index : ℕ, exceptional ×ˢ Set.Icc (-(index : ℝ)) (index : ℝ) := by
    intro point hpoint
    obtain ⟨index, hindex⟩ := exists_nat_gt |point.2|
    apply Set.mem_iUnion.mpr
    refine ⟨index, hpoint.1, ?_⟩
    have habs := abs_le.mp hindex.le
    exact habs
  calc
    _ ≤ dimH (⋃ index : ℕ, exceptional ×ˢ Set.Icc (-(index : ℝ)) (index : ℝ)) :=
      dimH_mono hcover
    _ = ⨆ index : ℕ, dimH (exceptional ×ˢ Set.Icc (-(index : ℝ)) (index : ℝ)) := dimH_iUnion _
    _ ≤ 1 := by
      apply iSup_le
      intro index
      simpa only [hexceptional, zero_add] using
        falconer2003_product73_interval exceptional (-(index : ℝ)) (index : ℝ) (by have hnonnegative : (0 : ℝ) ≤ index := Nat.cast_nonneg _; linarith)

/-- The sparse exceptional contraction set can be removed for all block
lengths and all slopes with a single exceptional parameter set of dimension
at most one. -/
theorem dimH_all_block_sparse_exceptions (exceptional : Set ℝ)
    (hexceptional : dimH exceptional = 0) :
    dimH ((⋃ power : {power : ℕ // 0 < power},
      {ratio : ℝ | 0 < ratio ∧ ratio ^ (power : ℕ) ∈ exceptional}) ×ˢ (Set.univ : Set ℝ)) ≤ 1 :=
  dimH_zero_exception_times_real _ (dimH_all_positive_power_preimages exceptional hexceptional)

end LambdaCantor.First.LinearRegularity


