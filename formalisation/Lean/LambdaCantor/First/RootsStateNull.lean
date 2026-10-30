import LambdaCantor.First.RootsStateDimension
import LambdaCantor.First.RootsIncidenceNull
import LambdaCantor.First.RootsCoordinateBounds
import LambdaCantor.First.RootFibreGeometry

noncomputable section
namespace LambdaCantor.First.Roots

open Set MeasureTheory

def rootFibreState {exponent : ℝ} (data : RootFibreData exponent)
    (digits : ℕ → Bool × Bool) : ℝ × ℝ :=
  incidenceState exponent ((data.leftLength : ℝ) - data.rightLength)
    (cylinderIncidencePoint data.root data.leftWord data.rightWord
      data.leftLength data.rightLength digits)

/-- Continuity of the actual state map, for compact good-state exhaustion. -/
theorem rootFibreData_continuous_state {exponent : ℝ} (data : RootFibreData exponent) :
    Continuous (rootFibreState data) := by
  have hparameter : ∀ digits, 0 < data.root digits := by
    intro digits
    linarith [data.lower_gt_quarter, (data.root_in_band digits).1]
  have hless : ∀ digits, data.root digits < 1 := by
    intro digits
    linarith [data.upper_lt_half, (data.root_in_band digits).2]
  have hincidence := continuous_cylinderIncidencePoint
    (by linarith [data.lower_gt_quarter] : 0 ≤ data.lower)
    (by linarith [data.upper_lt_half] : data.upper < 1) data.ordered
    data.root (rootFibreData_continuous_root data) data.root_in_band
    data.leftWord data.rightWord data.leftLength data.rightLength
  have hy : ∀ digits, (cylinderIncidencePoint data.root data.leftWord data.rightWord
      data.leftLength data.rightLength digits).2.2 ≠ 0 := by
    intro digits
    have hpositive := data.right_positive digits (data.root digits) (data.root_in_band digits)
    change address (data.root digits)
      (cylinderDigits data.rightWord data.rightLength (fun index => (digits index).2)) ≠ 0
    simpa only [cylinder_address (hparameter digits).le (hless digits), cylinderCoordinate] using
      hpositive.ne'
  have hratio := ((continuous_fst.comp (continuous_snd.comp hincidence)).div
    (continuous_snd.comp (continuous_snd.comp hincidence)) hy).rpow_const
      (fun _ => Or.inr (by linarith [data.exponent_gt_one] : 0 ≤ exponent - 1))
  have hparameterPower := (rootFibreData_continuous_root data).rpow_const
    (p := (data.leftLength : ℝ) - data.rightLength)
    (fun digits => Or.inl (hparameter digits).ne')
  exact (rootFibreData_continuous_root data).prodMk (hparameterPower.mul hratio)

/-- The genuine parameter/derivative-ratio state avoids every exceptional
state set of dimension at most one, almost surely. All compact patch and
inverse bounds are derived from the original concrete root-fibre data. -/
theorem rootFibreData_state_exceptional_null {exponent : ℝ} (data : RootFibreData exponent)
    {exceptional : Set (ℝ × ℝ)} (hdimension : dimH exceptional ≤ 1) :
    pairedAddressMeasure (rootFibreState data ⁻¹' exceptional) = 0 := by
  obtain ⟨coordinateLower, hcoordinate, hlower⟩ := rootFibreData_uniform_positive_coordinates data
  have hparameter : 0 < data.lower := by linarith [data.lower_gt_quarter]
  have hpatch : ∀ digits : ℕ → Bool × Bool,
      cylinderIncidencePoint data.root data.leftWord data.rightWord
        data.leftLength data.rightLength digits ∈
        positiveCurvePatch exponent data.lower data.upper coordinateLower := by
    intro digits
    have hnonnegative : 0 ≤ data.root digits :=
      hparameter.le.trans (data.root_in_band digits).1
    have hless : data.root digits < 1 := by
      linarith [data.upper_lt_half, (data.root_in_band digits).2]
    have hleft := address_le_one hnonnegative hless
      (cylinderDigits data.leftWord data.leftLength (fun index => (digits index).1))
    have hright := address_le_one hnonnegative hless
      (cylinderDigits data.rightWord data.rightLength (fun index => (digits index).2))
    have hcoordinates := hlower digits (data.root digits) (data.root_in_band digits)
    have hcurve := (rootFibreData_point_mem_intersection data digits).2.2
    change (data.root digits ∈ Set.Icc data.lower data.upper ∧
      (address (data.root digits) (cylinderDigits data.leftWord data.leftLength
        (fun index => (digits index).1)) ∈ Set.Icc coordinateLower 1 ∧
      address (data.root digits) (cylinderDigits data.rightWord data.rightLength
        (fun index => (digits index).2)) ∈ Set.Icc coordinateLower 1)) ∧ _
    constructor
    · refine ⟨data.root_in_band digits, ⟨?_, hleft⟩, ⟨?_, hright⟩⟩
      · simpa only [cylinder_address hnonnegative hless, cylinderCoordinate] using hcoordinates.1
      · simpa only [cylinder_address hnonnegative hless, cylinderCoordinate] using hcoordinates.2
    · simpa only [Set.mem_setOf_eq, cylinderIncidencePoint, cylinder_address hnonnegative hless,
        cylinderCoordinate] using hcurve
  have hstateDimension := (incidenceState_preimage_dimension
    (parameterUpper := data.upper)
    (shift := (data.leftLength : ℝ) - data.rightLength)
    data.exponent_gt_one hparameter hcoordinate exceptional).trans hdimension
  have hnull := cylinder_incidence_null_of_dimH_le_one data.lower_gt_quarter
    data.upper_lt_half data.root (rootFibreData_continuous_root data) data.root_in_band
    data.leftWord data.rightWord data.leftLength data.rightLength hstateDimension
  apply le_antisymm (le_trans (measure_mono ?_) hnull.le) zero_le
  intro digits hdigits
  exact ⟨hpatch digits, hdigits⟩

end LambdaCantor.First.Roots

#print axioms LambdaCantor.First.Roots.rootFibreData_continuous_state
#print axioms LambdaCantor.First.Roots.rootFibreData_state_exceptional_null
