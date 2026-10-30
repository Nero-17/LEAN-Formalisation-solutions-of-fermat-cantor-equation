import LambdaCantor.AE.AddressPairInverse
import Mathlib.Topology.Order.IntermediateValue

open Set

namespace LambdaCantor.AE

theorem isOpen_addressPairBand
    (first second third fourth : ℕ → Bool) {lower upper band : ℝ}
    (hdifferentiable : ∀ ratio ∈ Ioo lower upper,
      DifferentiableAt ℝ (addressPairDifference first second third fourth) ratio) :
    IsOpen (addressPairBand first second third fourth lower upper band) := by
  have hcontinuous : ContinuousOn (addressPairDifference first second third fourth)
      (Ioo lower upper) := fun ratio hratio =>
    (hdifferentiable ratio hratio).continuousAt.continuousWithinAt
  exact hcontinuous.isOpen_inter_preimage isOpen_Ioo isOpen_Ioo

/-- The actual band image is open. This uses the intermediate value theorem
between two nearby parameters on either side of each parameter, together
with strict antitonicity supplied by the saturation argument. -/
theorem isOpen_addressPairBand_image
    (first second third fourth : ℕ → Bool) {lower upper band : ℝ} (hband : 0 < band)
    (hdifferentiable : ∀ ratio ∈ Ioo lower upper,
      DifferentiableAt ℝ (addressPairDifference first second third fourth) ratio)
    (hnegative : ∀ ratio ∈ Ioo lower upper,
      |addressPairDifference first second third fourth ratio| < band →
        deriv (addressPairDifference first second third fourth) ratio < 0) :
    IsOpen (addressPairDifference first second third fourth ''
      addressPairBand first second third fourth lower upper band) := by
  have hopen := isOpen_addressPairBand first second third fourth (band := band) hdifferentiable
  have hanti := strictAntiOn_of_deriv_neg_on_band (convex_Ioo lower upper) hband
    hdifferentiable hnegative
  rw [isOpen_iff_mem_nhds]
  rintro value ⟨ratio, hratio, rfl⟩
  obtain ⟨leftEndpoint, rightEndpoint, hbetween, hsubset⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hratio)
  obtain ⟨left, hleftEndpoint, hleft⟩ := exists_between hbetween.1
  obtain ⟨right, hright, hrightEndpoint⟩ := exists_between hbetween.2
  have hclosed : Icc left right ⊆ addressPairBand first second third fourth lower upper band :=
    (Icc_subset_Ioo hleftEndpoint hrightEndpoint).trans hsubset
  have hleftmem := hclosed (left_mem_Icc.mpr (hleft.trans hright).le)
  have hrightmem := hclosed (right_mem_Icc.mpr (hleft.trans hright).le)
  have hcontinuous : ContinuousOn (addressPairDifference first second third fourth) (Icc left right) :=
    fun point hpoint => (hdifferentiable point (hclosed hpoint).1).continuousAt.continuousWithinAt
  apply Filter.mem_of_superset
    (Ioo_mem_nhds (hanti hratio hrightmem hright) (hanti hleftmem hratio hleft))
  intro nearby hnearby
  obtain ⟨parameter, hparameter, hequality⟩ := intermediate_value_Icc'
    (hleft.trans hright).le hcontinuous ⟨hnearby.1.le, hnearby.2.le⟩
  exact ⟨parameter, hclosed hparameter, hequality⟩

end LambdaCantor.AE
