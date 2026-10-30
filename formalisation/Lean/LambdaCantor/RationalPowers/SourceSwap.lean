import LambdaCantor.Classical.GeneralCoverLocal
import LambdaCantor.Classical.GeneralEventualIsolation

noncomputable section
namespace LambdaCantor.RationalPowers

-- Generic fibre swap lemmas copied from Integer.NearAxisReciprocalDimension.
theorem cantorLevel_swap_nonisolated (function : ℝ → ℝ → ℝ) (level : ℝ)
    (point : Classical.cantorLevel function level)
    (nonisolated : ¬ IsOpen ({point} : Set (Classical.cantorLevel function level))) :
    ¬ IsOpen ({(⟨(point.val.2,point.val.1),⟨⟨point.property.1.2,point.property.1.1⟩,
      point.property.2⟩⟩ : Classical.cantorLevel (fun x y => function y x) level)} :
      Set (Classical.cantorLevel (fun x y => function y x) level)) := by
  let swapMap : Classical.cantorLevel function level →
      Classical.cantorLevel (fun x y => function y x) level := fun value =>
    ⟨(value.val.2,value.val.1),⟨⟨value.property.1.2,value.property.1.1⟩,value.property.2⟩⟩
  have continuousMap : Continuous swapMap :=
    (continuous_swap.comp continuous_subtype_val).subtype_mk _
  intro isolated
  have preimage := isolated.preimage continuousMap
  have equality : swapMap ⁻¹' {swapMap point} = {point} := by
    ext value
    simp only [Set.mem_preimage,Set.mem_singleton_iff]
    constructor
    · intro equal
      apply Subtype.ext
      have coordinates := congrArg Subtype.val equal
      apply Prod.ext
      · exact congrArg Prod.snd coordinates
      · exact congrArg Prod.fst coordinates
    · intro equal
      rw [equal]
  apply nonisolated
  rwa [equality] at preimage

theorem cantorLevel_swap_dimH (function : ℝ → ℝ → ℝ) (level : ℝ) :
    dimH (Classical.cantorLevel (fun x y => function y x) level) =
      dimH (Classical.cantorLevel function level) := by
  have isometry : Isometry (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
    Isometry.of_dist_eq (fun first second => by
      simp only [Prod.dist_eq]
      exact max_comm _ _)
  have equality : Prod.swap '' Classical.cantorLevel function level =
      Classical.cantorLevel (fun x y => function y x) level := by
    ext point
    constructor
    · rintro ⟨value,member,rfl⟩
      exact ⟨⟨member.1.2,member.1.1⟩,member.2⟩
    · intro member
      exact ⟨(point.2,point.1),⟨⟨member.1.2,member.1.1⟩,member.2⟩,rfl⟩
  rw [← equality]
  exact isometry.dimH_image _


theorem coordinateBounds_swap (function : ℝ → ℝ → ℝ) (a b c d : ℝ)
    (bounds : Classical.CoordinateBounds function a b c d) :
    Classical.CoordinateBounds (fun x y => function y x) c d a b :=
  ⟨bounds.vertical,bounds.horizontal⟩

theorem continuousOn_swap (function : ℝ → ℝ → ℝ)
    (continuous : ContinuousOn (fun point : ℝ × ℝ => function point.1 point.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun point : ℝ × ℝ => function point.2 point.1)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
  continuous.comp (continuous_snd.prodMk continuous_fst).continuousOn
    (fun _ membership => ⟨membership.2,membership.1⟩)

end LambdaCantor.RationalPowers
