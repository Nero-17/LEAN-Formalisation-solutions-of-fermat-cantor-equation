import LambdaCantor.AE.AddressPairKernel
import LambdaCantor.AE.BandMonotonicity
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open Set Filter
open scoped Topology

namespace LambdaCantor.AE

/-- The near-zero parameter band for the actual four-address residual. -/
def addressPairBand (first second third fourth : ℕ → Bool) (lower upper band : ℝ) : Set ℝ :=
  Ioo lower upper ∩ addressPairDifference first second third fourth ⁻¹' Ioo (-band) band

/-- Canonical inverse on the actual near-zero band. Its values outside the
image are irrelevant; all regularity statements below specify that image. -/
def addressPairInverse (first second third fourth : ℕ → Bool) (lower upper band : ℝ) : ℝ → ℝ :=
  Function.invFunOn (addressPairDifference first second third fourth)
    (addressPairBand first second third fourth lower upper band)

theorem addressPairInverse_mem_and_right_inverse
    (first second third fourth : ℕ → Bool) (lower upper band : ℝ) {value : ℝ}
    (hvalue : value ∈ addressPairDifference first second third fourth ''
      addressPairBand first second third fourth lower upper band) :
    addressPairInverse first second third fourth lower upper band value ∈
        addressPairBand first second third fourth lower upper band ∧
      addressPairDifference first second third fourth
        (addressPairInverse first second third fourth lower upper band value) = value := by
  exact Function.invFunOn_pos hvalue

/-- Quantitative continuity of the canonical inverse. Convexity of the band
is derived from the sign condition, not assumed as a further hypothesis. -/
theorem lipschitzOnWith_addressPairInverse
    (first second third fourth : ℕ → Bool) {lower upper band margin : ℝ}
    (hband : 0 < band) (hmargin : 0 < margin)
    (hdifferentiable : ∀ ratio ∈ Ioo lower upper,
      DifferentiableAt ℝ (addressPairDifference first second third fourth) ratio)
    (hderivative : ∀ ratio ∈ Ioo lower upper,
      |addressPairDifference first second third fourth ratio| < band →
        deriv (addressPairDifference first second third fourth) ratio ≤ -margin) :
    LipschitzOnWith ⟨margin⁻¹, inv_nonneg.mpr hmargin.le⟩
      (addressPairInverse first second third fourth lower upper band)
      (addressPairDifference first second third fourth ''
        addressPairBand first second third fourth lower upper band) := by
  change LipschitzOnWith (NNReal.mk margin⁻¹ (inv_nonneg.mpr hmargin.le))
    (addressPairInverse first second third fourth lower upper band)
    (addressPairDifference first second third fourth ''
      addressPairBand first second third fourth lower upper band)
  have hnegative : ∀ ratio ∈ Ioo lower upper,
      |addressPairDifference first second third fourth ratio| < band →
        deriv (addressPairDifference first second third fourth) ratio < 0 := by
    intro ratio hratio hsmall
    exact (hderivative ratio hratio hsmall).trans_lt (neg_neg_of_pos hmargin)
  have hconvex : Convex ℝ (addressPairBand first second third fourth lower upper band) :=
    convex_preimage_band_of_antitone_primitive (convex_Ioo _ _) hband
      (antitoneOn_bandPrimitive_comp (convex_Ioo _ _) hband hdifferentiable hnegative)
  have hslope : ∀ left ∈ addressPairBand first second third fourth lower upper band,
      ∀ right ∈ addressPairBand first second third fourth lower upper band, left ≤ right →
        addressPairDifference first second third fourth right -
          addressPairDifference first second third fourth left ≤ -margin * (right - left) := by
    intro left hleft right hright horder
    apply hconvex.image_sub_le_mul_sub_of_deriv_le ?_ ?_ ?_ left hleft right hright horder
    · intro ratio hratio
      exact (hdifferentiable ratio hratio.1).continuousAt.continuousWithinAt
    · intro ratio hratio
      exact (hdifferentiable ratio (interior_subset hratio).1).differentiableWithinAt
    · intro ratio hratio
      exact hderivative ratio (interior_subset hratio).1
        (abs_lt.mpr (interior_subset hratio).2)
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro left hleft right hright
  obtain ⟨hleftmem, hleftinverse⟩ :=
    addressPairInverse_mem_and_right_inverse first second third fourth lower upper band hleft
  obtain ⟨hrightmem, hrightinverse⟩ :=
    addressPairInverse_mem_and_right_inverse first second third fourth lower upper band hright
  have hbound : margin *
      |addressPairInverse first second third fourth lower upper band left -
        addressPairInverse first second third fourth lower upper band right| ≤ |left - right| := by
    by_cases horder : addressPairInverse first second third fourth lower upper band left ≤
        addressPairInverse first second third fourth lower upper band right
    · have hs := hslope _ hleftmem _ hrightmem horder
      rw [hleftinverse, hrightinverse] at hs
      rw [abs_of_nonpos (sub_nonpos.mpr horder)]
      nlinarith [le_abs_self (left - right)]
    · have hs := hslope _ hrightmem _ hleftmem (le_of_not_ge horder)
      rw [hleftinverse, hrightinverse] at hs
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge horder))]
      nlinarith [neg_le_abs (left - right)]
  simp only [Real.dist_eq, NNReal.coe_mk]
  have hdivide :
      |addressPairInverse first second third fourth lower upper band left -
        addressPairInverse first second third fourth lower upper band right| ≤ |left - right| / margin :=
    (le_div_iff₀ hmargin).mpr (by simpa only [mul_comm] using hbound)
  simpa only [div_eq_mul_inv, mul_comm] using hdivide

/-- The inverse derivative is proved for the canonical inverse, using its
quantitative continuity and local right-inverse identity. -/
theorem hasDerivAt_addressPairInverse
    (first second third fourth : ℕ → Bool) {lower upper band margin value : ℝ}
    (hband : 0 < band) (hmargin : 0 < margin)
    (hdifferentiable : ∀ ratio ∈ Ioo lower upper,
      DifferentiableAt ℝ (addressPairDifference first second third fourth) ratio)
    (hderivative : ∀ ratio ∈ Ioo lower upper,
      |addressPairDifference first second third fourth ratio| < band →
        deriv (addressPairDifference first second third fourth) ratio ≤ -margin)
    (hvalue : value ∈ interior (addressPairDifference first second third fourth ''
      addressPairBand first second third fourth lower upper band)) :
    HasDerivAt (addressPairInverse first second third fourth lower upper band)
      (deriv (addressPairDifference first second third fourth)
        (addressPairInverse first second third fourth lower upper band value))⁻¹ value := by
  have hmembership := addressPairInverse_mem_and_right_inverse first second third fourth
    lower upper band (interior_subset hvalue)
  have hcontinuous := (lipschitzOnWith_addressPairInverse first second third fourth
    hband hmargin hdifferentiable hderivative).continuousOn
  have hne : deriv (addressPairDifference first second third fourth)
      (addressPairInverse first second third fourth lower upper band value) ≠ 0 :=
    ne_of_lt ((hderivative _ hmembership.1.1 (abs_lt.mpr hmembership.1.2)).trans_lt
      (neg_neg_of_pos hmargin))
  apply HasDerivAt.of_local_left_inverse
    ((hcontinuous value (interior_subset hvalue)).continuousAt (mem_interior_iff_mem_nhds.mp hvalue))
    (hdifferentiable _ hmembership.1.1).hasDerivAt hne
  filter_upwards [mem_interior_iff_mem_nhds.mp hvalue] with nearby hnearby
  exact (addressPairInverse_mem_and_right_inverse first second third fourth lower upper band hnearby).2

end LambdaCantor.AE
