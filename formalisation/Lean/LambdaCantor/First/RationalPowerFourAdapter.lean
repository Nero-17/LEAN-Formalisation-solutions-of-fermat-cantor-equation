import LambdaCantor.First.RationalPowerFourRoots
import LambdaCantor.First.RealNormalizationPrefixes
import LambdaCantor.First.RootContinuity
import LambdaCantor.ParameterContinuity
import Mathlib.Topology.Order.Compact

noncomputable section
open scoped BigOperators
namespace LambdaCantor.First.Roots

/-- Joint continuity of the actual cylinder residual on an arbitrary
positive compact band; it does not require pre-existing root data. -/
theorem continuous_cylinderResidual_on_band {exponent lower upper : ℝ}
    (hexponent : 0 ≤ exponent) (hlower : 0 ≤ lower) (hupper : upper < 1)
    (hordered : lower ≤ upper) (leftWord rightWord : ℕ → Bool)
    (leftLength rightLength : ℕ) :
    Continuous (fun point : (ℕ → Bool × Bool) × Set.Icc lower upper =>
      cylinderResidual exponent leftWord rightWord leftLength rightLength point.1 point.2) := by
  have haddress := continuous_address_band hlower hupper hordered
  have hcoordinates : ∀ (word : ℕ → Bool) (length : ℕ) (coordinate : Bool × Bool → Bool),
      Continuous coordinate →
      Continuous (fun point : (ℕ → Bool × Bool) × Set.Icc lower upper =>
        cylinderCoordinate word length (fun index => coordinate (point.1 index)) point.2) := by
    intro word length coordinate hcoordinate
    have hdigits : Continuous (fun digits : ℕ → Bool × Bool => fun index => coordinate (digits index)) :=
      continuous_pi (fun index => hcoordinate.comp (continuous_apply index))
    have hprefix : Continuous (fun ratio : ℝ => prefixValue ratio word length) := by
      unfold prefixValue
      fun_prop
    exact (hprefix.comp (continuous_subtype_val.comp continuous_snd)).add
      (((continuous_subtype_val.comp continuous_snd).pow length).mul
        (haddress.comp (continuous_snd.prodMk (hdigits.comp continuous_fst))))
  exact (((hcoordinates leftWord leftLength Prod.fst continuous_fst).rpow_const
    (fun _ => Or.inr hexponent)).add
      ((hcoordinates rightWord rightLength Prod.snd continuous_snd).rpow_const
        (fun _ => Or.inr hexponent))).sub continuous_const

/-- A closed parameter band containing only interior roots can be reduced
to one compact band strictly above one quarter. -/
theorem rootFibreData_of_interior_roots {exponent upper : ℝ}
    (hexponent : 1 < exponent) (hupper : upper < 1 / 2)
    (leftWord rightWord : ℕ → Bool) (leftLength rightLength : ℕ)
    (root : (ℕ → Bool × Bool) → ℝ)
    (hroot : ∀ digits, root digits ∈ Set.Ioo (1 / 4 : ℝ) upper)
    (hcontinuous : Continuous
      (fun point : (ℕ → Bool × Bool) × Set.Icc (1 / 4 : ℝ) upper =>
        cylinderResidual exponent leftWord rightWord leftLength rightLength point.1 point.2))
    (hleft : ∀ (digits : ℕ → Bool × Bool) ratio, ratio ∈ Set.Icc (1 / 4 : ℝ) upper →
      0 < cylinderCoordinate leftWord leftLength (fun index => (digits index).1) ratio)
    (hright : ∀ (digits : ℕ → Bool × Bool) ratio, ratio ∈ Set.Icc (1 / 4 : ℝ) upper →
      0 < cylinderCoordinate rightWord rightLength (fun index => (digits index).2) ratio)
    (hunique : ∀ digits ratio, ratio ∈ Set.Icc (1 / 4 : ℝ) upper →
      (cylinderResidual exponent leftWord rightWord leftLength rightLength digits ratio = 0 ↔
        ratio = root digits))
    (bound : ℝ) (hbound : 0 < bound)
    (htransverse : ∀ digits, bound ≤
      |deriv (cylinderResidual exponent leftWord rightWord leftLength rightLength digits) (root digits)|) :
    ∃ data : RootFibreData exponent, data.upper < upper := by
  let subtypeRoot : (ℕ → Bool × Bool) → Set.Icc (1 / 4 : ℝ) upper :=
    fun digits => ⟨root digits, ⟨(hroot digits).1.le, (hroot digits).2.le⟩⟩
  have hrootContinuous : Continuous root := by
    apply continuous_subtype_val.comp
      (continuous_unique_root _ hcontinuous subtypeRoot _ _)
    · intro digits
      exact (hunique digits (root digits) ⟨(hroot digits).1.le, (hroot digits).2.le⟩).mpr rfl
    · intro digits ratio hzero
      apply Subtype.ext
      exact (hunique digits ratio ratio.property).mp hzero
  have hcompact : IsCompact (Set.range root) := isCompact_range hrootContinuous
  have hnonempty : (Set.range root).Nonempty := ⟨root (fun _ => (false, false)), Set.mem_range_self _⟩
  obtain ⟨lower, hlower⟩ := hcompact.exists_isLeast hnonempty
  obtain ⟨ceiling, hceiling⟩ := hcompact.exists_isGreatest hnonempty
  have hlowerQuarter : (1 / 4 : ℝ) < lower := by
    obtain ⟨digits, rfl⟩ := hlower.1
    exact (hroot digits).1
  have hceilingUpper : ceiling < upper := by
    obtain ⟨digits, rfl⟩ := hceiling.1
    exact (hroot digits).2
  have hband (ratio : ℝ) (hratio : ratio ∈ Set.Icc lower ceiling) :
      ratio ∈ Set.Icc (1 / 4 : ℝ) upper :=
    ⟨hlowerQuarter.le.trans hratio.1, hratio.2.trans hceilingUpper.le⟩
  refine ⟨{
    exponent_gt_one := hexponent
    lower := lower
    upper := ceiling
    lower_gt_quarter := hlowerQuarter
    upper_lt_half := hceilingUpper.trans hupper
    ordered := hlower.2 hceiling.1
    leftWord := leftWord
    rightWord := rightWord
    leftLength := leftLength
    rightLength := rightLength
    root := root
    root_in_band := fun digits =>
      ⟨hlower.2 (Set.mem_range_self digits), hceiling.2 (Set.mem_range_self digits)⟩
    left_positive := fun digits ratio hratio => hleft digits ratio (hband ratio hratio)
    right_positive := fun digits ratio hratio => hright digits ratio (hband ratio hratio)
    unique_root := fun digits ratio hratio => hunique digits ratio (hband ratio hratio)
    derivative_lower_bound := bound
    derivative_lower_bound_positive := hbound
    transverse := htransverse }, hceilingUpper⟩

/-- The actual powers-four left cylinder has prefix zero repeated k times
followed by one repeated L times. -/
def powersFourLeftPrefix (depth : ℕ) (index : ℕ) : Bool := decide (depth ≤ index)

theorem powersFourLeftPrefix_coordinate (ratio : ℝ) (depth padding : ℕ)
    (digits : ℕ → Bool) :
    cylinderCoordinate (powersFourLeftPrefix depth) (depth + padding) digits ratio =
      ratio ^ depth * powersFourLeftFactor padding digits ratio := by
  have hfirst : (∑ index ∈ Finset.range depth,
      (if powersFourLeftPrefix depth index then (1 : ℝ) else 0) * ratio ^ index) = 0 := by
    apply Finset.sum_eq_zero
    intro index hindex
    simp [powersFourLeftPrefix, not_le.mpr (Finset.mem_range.mp hindex)]
  have hsecond : (∑ index ∈ Finset.range padding,
      (if powersFourLeftPrefix depth (depth + index) then (1 : ℝ) else 0) *
        ratio ^ (depth + index)) = ratio ^ depth * ∑ index ∈ Finset.range padding, ratio ^ index := by
    simp [powersFourLeftPrefix, pow_add, Finset.mul_sum]
  have hprefix : prefixValue ratio (powersFourLeftPrefix depth) (depth + padding) =
      ratio ^ depth * (1 - ratio ^ padding) := by
    unfold prefixValue
    rw [Finset.sum_range_add, hfirst, hsecond, zero_add]
    calc
      _ = ratio ^ depth * ((∑ index ∈ Finset.range padding, ratio ^ index) * (1 - ratio)) := by ring
      _ = _ := by rw [geom_sum_mul_neg]
  rw [cylinderCoordinate, hprefix, pow_add]
  unfold powersFourLeftFactor
  ring

/-- The cylinder residual is the actual integer-power numerator used in
the powers-four estimates, with no limiting replacement. -/
theorem powersFourPrefix_residual (exponent phase index : ℕ)
    (digits : ℕ → Bool × Bool) (ratio : ℝ) :
    cylinderResidual (exponent : ℝ)
      (powersFourLeftPrefix index) (realRootRightPrefix (exponent * index + phase))
      (index + (exponent * index + phase + phase + 2))
      ((exponent * index + phase) + (exponent * index + phase + phase + 2)) digits ratio =
      (ratio ^ index * powersFourLeftFactor (exponent * index + phase + phase + 2)
        (fun index => (digits index).1) ratio) ^ exponent +
      (1 - ratio ^ (exponent * index + phase) +
        ratio ^ ((exponent * index + phase) + (exponent * index + phase + phase + 2)) *
          address ratio (fun index => (digits index).2)) ^ exponent - 1 := by
  rw [cylinderResidual, powersFourLeftPrefix_coordinate, realRootRightPrefix_coordinate,
    firstRootY, Real.rpow_natCast, Real.rpow_natCast]

end LambdaCantor.First.Roots
