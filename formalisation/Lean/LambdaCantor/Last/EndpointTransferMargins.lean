import LambdaCantor.Last.TwoBandCriterion
import Mathlib.Tactic.FunProp

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

theorem exists_two_band_vertical_margin {ratio lowerS upperS center : ℝ}
    (hlowerS : 0 < lowerS) (horderS : lowerS ≤ upperS) (hcenter : 0 < center)
    (bands : TwoBandInterval ratio (center / upperS) (center / lowerS)) :
    ∃ epsilon > 0, 0 < center - epsilon ∧
      TwoBandInterval ratio ((center - epsilon) / upperS) ((center + epsilon) / lowerS) := by
  have hupperS : 0 < upperS := hlowerS.trans_le horderS
  have hmargin : ∀ lowerBound upperBound : ℝ,
      lowerBound < center / upperS → center / lowerS < upperBound →
      ∃ epsilon > 0, 0 < center - epsilon ∧ 1 < (center - epsilon) / upperS ∧
        lowerBound < (center - epsilon) / upperS ∧ (center + epsilon) / lowerS < upperBound := by
    intro lowerBound upperBound hlower hupper
    have hpositive_eventual : ∀ᶠ epsilon : ℝ in 𝓝 0, 0 < center - epsilon :=
      (show Continuous (fun epsilon : ℝ => center - epsilon) by fun_prop).continuousAt.eventually
        (lt_mem_nhds (by simpa using hcenter))
    have hone_eventual : ∀ᶠ epsilon : ℝ in 𝓝 0, 1 < (center - epsilon) / upperS :=
      (show Continuous (fun epsilon : ℝ => (center - epsilon) / upperS) by fun_prop).continuousAt.eventually
        (lt_mem_nhds (by simpa using bands.1))
    have hlower_eventual : ∀ᶠ epsilon : ℝ in 𝓝 0, lowerBound < (center - epsilon) / upperS :=
      (show Continuous (fun epsilon : ℝ => (center - epsilon) / upperS) by fun_prop).continuousAt.eventually
        (lt_mem_nhds (by simpa using hlower))
    have hupper_eventual : ∀ᶠ epsilon : ℝ in 𝓝 0, (center + epsilon) / lowerS < upperBound :=
      (show Continuous (fun epsilon : ℝ => (center + epsilon) / lowerS) by fun_prop).continuousAt.eventually
        (gt_mem_nhds (by simpa using hupper))
    obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp
      (hpositive_eventual.and (hone_eventual.and (hlower_eventual.and hupper_eventual)))
    have hhalf : radius / 2 ∈ Metric.ball (0 : ℝ) radius := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
      linarith
    exact ⟨radius / 2, by linarith, hball hhalf⟩
  have horder : ∀ epsilon : ℝ, 0 < epsilon →
      (center - epsilon) / upperS ≤ (center + epsilon) / lowerS := by
    intro epsilon hepsilon
    exact div_le_div₀ (by linarith) (by linarith) hlowerS horderS
  rcases bands.2.2 with first | second
  · obtain ⟨epsilon, hepsilon, hcenter_epsilon, hone, hlower, hupper⟩ :=
      hmargin _ _ first.1 first.2
    exact ⟨epsilon, hepsilon, hcenter_epsilon, hone, horder epsilon hepsilon, Or.inl ⟨hlower, hupper⟩⟩
  · obtain ⟨epsilon, hepsilon, hcenter_epsilon, hone, hlower, hupper⟩ :=
      hmargin _ _ second.1 second.2
    exact ⟨epsilon, hepsilon, hcenter_epsilon, hone, horder epsilon hepsilon, Or.inr ⟨hlower, hupper⟩⟩

theorem exists_two_band_horizontal_margin {ratio lowerS upperS lowerT upperT : ℝ}
    (hlowerS : 0 < lowerS) (horderS : lowerS ≤ upperS) (horderT : lowerT ≤ upperT)
    (bands : TwoBandInterval ratio (lowerT / upperS) (upperT / lowerS)) :
    ∃ epsilon > 0, 0 < lowerS - epsilon ∧
      TwoBandInterval ratio (lowerT / (upperS + epsilon)) (upperT / (lowerS - epsilon)) := by
  have hupperS : 0 < upperS := hlowerS.trans_le horderS
  have hlowerT : 0 < lowerT := by
    have hbound := (lt_div_iff₀ hupperS).mp bands.1
    nlinarith
  have hupperT : 0 < upperT := hlowerT.trans_le horderT
  have hlow_continuous : ContinuousAt (fun epsilon : ℝ => lowerT / (upperS + epsilon)) 0 :=
    continuousAt_const.div (continuous_const.add continuous_id).continuousAt (by simpa using hupperS.ne')
  have hupp_continuous : ContinuousAt (fun epsilon : ℝ => upperT / (lowerS - epsilon)) 0 :=
    continuousAt_const.div (continuous_const.sub continuous_id).continuousAt (by simpa using hlowerS.ne')
  have hmargin : ∀ lowerBound upperBound : ℝ,
      lowerBound < lowerT / upperS → upperT / lowerS < upperBound →
      ∃ epsilon > 0, 0 < lowerS - epsilon ∧ 1 < lowerT / (upperS + epsilon) ∧
        lowerBound < lowerT / (upperS + epsilon) ∧ upperT / (lowerS - epsilon) < upperBound := by
    intro lowerBound upperBound hlower hupper
    have hpositive_eventual : ∀ᶠ epsilon : ℝ in 𝓝 0, 0 < lowerS - epsilon :=
      (continuous_const.sub continuous_id).continuousAt.eventually
        (lt_mem_nhds (by simpa using hlowerS))
    have hone_eventual : ∀ᶠ epsilon : ℝ in 𝓝 0, 1 < lowerT / (upperS + epsilon) :=
      hlow_continuous.eventually (lt_mem_nhds (by simpa using bands.1))
    have hlower_eventual : ∀ᶠ epsilon : ℝ in 𝓝 0, lowerBound < lowerT / (upperS + epsilon) :=
      hlow_continuous.eventually (lt_mem_nhds (by simpa using hlower))
    have hupper_eventual : ∀ᶠ epsilon : ℝ in 𝓝 0, upperT / (lowerS - epsilon) < upperBound :=
      hupp_continuous.eventually (gt_mem_nhds (by simpa using hupper))
    obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp
      (hpositive_eventual.and (hone_eventual.and (hlower_eventual.and hupper_eventual)))
    have hhalf : radius / 2 ∈ Metric.ball (0 : ℝ) radius := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
      linarith
    exact ⟨radius / 2, by linarith, hball hhalf⟩
  have horder : ∀ epsilon : ℝ, 0 < epsilon → 0 < lowerS - epsilon →
      lowerT / (upperS + epsilon) ≤ upperT / (lowerS - epsilon) := by
    intro epsilon hepsilon hdenominator
    exact div_le_div₀ hupperT.le horderT hdenominator (by linarith)
  rcases bands.2.2 with first | second
  · obtain ⟨epsilon, hepsilon, hpositive, hone, hlower, hupper⟩ := hmargin _ _ first.1 first.2
    exact ⟨epsilon, hepsilon, hpositive, hone, horder epsilon hepsilon hpositive, Or.inl ⟨hlower, hupper⟩⟩
  · obtain ⟨epsilon, hepsilon, hpositive, hone, hlower, hupper⟩ := hmargin _ _ second.1 second.2
    exact ⟨epsilon, hepsilon, hpositive, hone, horder epsilon hepsilon hpositive, Or.inr ⟨hlower, hupper⟩⟩

end LambdaCantor.Last
