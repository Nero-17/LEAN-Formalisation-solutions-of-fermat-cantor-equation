import LambdaCantor.First.RootFibreInterface
import LambdaCantor.First.RootContinuity
import LambdaCantor.ParameterContinuity

noncomputable section
namespace LambdaCantor.First.Roots

open MeasureTheory

theorem continuous_cylinderResidual_band {exponent : ℝ} (data : RootFibreData exponent) :
    Continuous (fun point : (ℕ → Bool × Bool) × Set.Icc data.lower data.upper =>
      cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength
        point.1 point.2) := by
  have hlower : 0 ≤ data.lower := by linarith [data.lower_gt_quarter]
  have hupper : data.upper < 1 := by linarith [data.upper_lt_half]
  have haddress := continuous_address_band hlower hupper data.ordered
  have hcoordinates : ∀ (word : ℕ → Bool) (length : ℕ) (coordinate : Bool × Bool → Bool),
      Continuous coordinate →
      Continuous (fun point : (ℕ → Bool × Bool) × Set.Icc data.lower data.upper =>
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
  have hleft := hcoordinates data.leftWord data.leftLength Prod.fst continuous_fst
  have hright := hcoordinates data.rightWord data.rightLength Prod.snd continuous_snd
  have hexponent : 0 ≤ exponent := by linarith [data.exponent_gt_one]
  exact ((hleft.rpow_const (fun _ => Or.inr hexponent)).add
    (hright.rpow_const (fun _ => Or.inr hexponent))).sub continuous_const

/-- Root continuity is derived from the concrete data, not included as an
extra root-fibre hypothesis. -/
theorem rootFibreData_continuous_root {exponent : ℝ} (data : RootFibreData exponent) :
    Continuous data.root := by
  let subtypeRoot : (ℕ → Bool × Bool) → Set.Icc data.lower data.upper :=
    fun digits => ⟨data.root digits, data.root_in_band digits⟩
  have hcontinuous : Continuous subtypeRoot :=
    continuous_unique_root
      (fun point : (ℕ → Bool × Bool) × Set.Icc data.lower data.upper =>
        cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength
          point.1 point.2)
      (continuous_cylinderResidual_band data) subtypeRoot
      (fun digits => (data.unique_root digits (data.root digits) (data.root_in_band digits)).mpr rfl)
      (by
        intro digits parameter hzero
        apply Subtype.ext
        exact (data.unique_root digits parameter parameter.property).mp hzero)
  exact continuous_subtype_val.comp hcontinuous

theorem rootFibreData_rootLaw_probability {exponent : ℝ} (data : RootFibreData exponent) :
    IsProbabilityMeasure (rootLaw data.root) :=
  rootLaw_probability data.root (rootFibreData_continuous_root data).measurable

theorem rootFibreData_rootLaw_parameter_band {exponent : ℝ} (data : RootFibreData exponent) :
    rootLaw data.root (Set.Icc data.lower data.upper) = 1 :=
  rootLaw_parameter_band data.root (rootFibreData_continuous_root data).measurable
    data.lower data.upper data.root_in_band

end LambdaCantor.First.Roots
