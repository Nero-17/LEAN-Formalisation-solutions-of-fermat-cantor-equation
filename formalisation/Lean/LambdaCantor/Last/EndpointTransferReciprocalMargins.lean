import LambdaCantor.Last.EndpointTransferMargins

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

theorem exists_two_band_reciprocal_vertical_margin {ratio lowerS upperS center : ℝ}
    (hlowerS : 0 < lowerS) (horderS : lowerS ≤ upperS) (hcenter : 0 < center)
    (bands : TwoBandInterval ratio (lowerS / center) (upperS / center)) :
    ∃ epsilon > 0, 0 < center - epsilon ∧
      TwoBandInterval ratio (lowerS / (center + epsilon)) (upperS / (center - epsilon)) :=
  exists_two_band_horizontal_margin hcenter (le_refl _) horderS bands

/-- Strict reciprocal bands tolerate the same horizontal derivative error
used by the actual logarithmic source. -/
theorem exists_two_band_reciprocal_horizontal_margin {ratio lowerS upperS lowerT upperT : ℝ}
    (hlowerS : 0 < lowerS) (horderS : lowerS ≤ upperS)
    (hlowerT : 0 < lowerT) (horderT : lowerT ≤ upperT)
    (bands : TwoBandInterval ratio (lowerS / upperT) (upperS / lowerT)) :
    ∃ epsilon > 0, 0 < lowerS - epsilon ∧
      TwoBandInterval ratio ((lowerS - epsilon) / upperT) ((upperS + epsilon) / lowerT) := by
  have hupperS : 0 < upperS := hlowerS.trans_le horderS
  have hupperT : 0 < upperT := hlowerT.trans_le horderT
  have hmargin : ∀ lowerBound upperBound : ℝ,
      lowerBound < lowerS / upperT → upperS / lowerT < upperBound →
      ∃ epsilon > 0, 0 < lowerS - epsilon ∧ 1 < (lowerS - epsilon) / upperT ∧
        lowerBound < (lowerS - epsilon) / upperT ∧ (upperS + epsilon) / lowerT < upperBound := by
    intro lowerBound upperBound hlower hupper
    have hpositive_eventual : ∀ᶠ epsilon : ℝ in 𝓝 0, 0 < lowerS - epsilon :=
      (show Continuous (fun epsilon : ℝ => lowerS - epsilon) by fun_prop).continuousAt.eventually
        (lt_mem_nhds (by simpa using hlowerS))
    have hone_eventual : ∀ᶠ epsilon : ℝ in 𝓝 0, 1 < (lowerS - epsilon) / upperT :=
      (show Continuous (fun epsilon : ℝ => (lowerS - epsilon) / upperT) by fun_prop).continuousAt.eventually
        (lt_mem_nhds (by simpa using bands.1))
    have hlower_eventual : ∀ᶠ epsilon : ℝ in 𝓝 0, lowerBound < (lowerS - epsilon) / upperT :=
      (show Continuous (fun epsilon : ℝ => (lowerS - epsilon) / upperT) by fun_prop).continuousAt.eventually
        (lt_mem_nhds (by simpa using hlower))
    have hupper_eventual : ∀ᶠ epsilon : ℝ in 𝓝 0, (upperS + epsilon) / lowerT < upperBound :=
      (show Continuous (fun epsilon : ℝ => (upperS + epsilon) / lowerT) by fun_prop).continuousAt.eventually
        (gt_mem_nhds (by simpa using hupper))
    obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp
      (hpositive_eventual.and (hone_eventual.and (hlower_eventual.and hupper_eventual)))
    have hhalf : radius / 2 ∈ Metric.ball (0 : ℝ) radius := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
      linarith
    exact ⟨radius / 2, by linarith, hball hhalf⟩
  have horder : ∀ epsilon : ℝ, 0 < epsilon →
      (lowerS - epsilon) / upperT ≤ (upperS + epsilon) / lowerT := by
    intro epsilon hepsilon
    exact div_le_div₀ (by linarith) (by linarith) hlowerT horderT
  rcases bands.2.2 with first | second
  · obtain ⟨epsilon, hepsilon, hpositive, hone, hlower, hupper⟩ := hmargin _ _ first.1 first.2
    exact ⟨epsilon, hepsilon, hpositive, hone, horder epsilon hepsilon, Or.inl ⟨hlower, hupper⟩⟩
  · obtain ⟨epsilon, hepsilon, hpositive, hone, hlower, hupper⟩ := hmargin _ _ second.1 second.2
    exact ⟨epsilon, hepsilon, hpositive, hone, horder epsilon hepsilon, Or.inr ⟨hlower, hupper⟩⟩

end LambdaCantor.Last
