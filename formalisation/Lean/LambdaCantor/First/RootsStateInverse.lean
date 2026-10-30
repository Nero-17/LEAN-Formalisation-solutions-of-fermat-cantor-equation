import LambdaCantor.First.RootsState
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
namespace LambdaCantor.First.Roots

open Set
open scoped NNReal

/-- The parameter and derivative-ratio state. Taking shift = h - ell gives
the manuscript's cylinder state. -/
def incidenceState (exponent shift : ℝ) (point : ℝ × ℝ × ℝ) : ℝ × ℝ :=
  (point.1, point.1 ^ shift * (point.2.1 / point.2.2) ^ (exponent - 1))

def recoveredCoordinateRatio (exponent shift : ℝ) (state : ℝ × ℝ) : ℝ :=
  (state.2 * state.1 ^ (-shift)) ^ (exponent - 1)⁻¹

theorem recoveredCoordinateRatio_incidenceState {exponent shift : ℝ}
    (hexponent : 1 < exponent) {point : ℝ × ℝ × ℝ}
    (hparameter : 0 < point.1) (hx : 0 < point.2.1) (hy : 0 < point.2.2) :
    recoveredCoordinateRatio exponent shift (incidenceState exponent shift point) =
      point.2.1 / point.2.2 := by
  unfold recoveredCoordinateRatio incidenceState
  dsimp
  have hpower : point.1 ^ shift ≠ 0 := (Real.rpow_pos_of_pos hparameter _).ne'
  rw [Real.rpow_neg hparameter.le]
  have hcancel : point.1 ^ shift * (point.2.1 / point.2.2) ^ (exponent - 1) *
      (point.1 ^ shift)⁻¹ = (point.2.1 / point.2.2) ^ (exponent - 1) := by
    field_simp [hpower] <;> ring
  rw [hcancel, ← Real.rpow_mul (div_pos hx hy).le,
    mul_inv_cancel₀ (by linarith : exponent - 1 ≠ 0), Real.rpow_one]

theorem recoveredCoordinateRatio_contDiffOn (exponent shift : ℝ) :
    ContDiffOn ℝ 1 (recoveredCoordinateRatio exponent shift)
      ((Set.Ioi (0 : ℝ)).prod (Set.Ioi (0 : ℝ))) := by
  apply (contDiffOn_snd.mul (contDiffOn_fst.rpow_const_of_ne
    (fun state hstate => hstate.1.ne'))).rpow_const_of_ne
  intro state hstate
  exact (mul_pos hstate.2 (Real.rpow_pos_of_pos hstate.1 _)).ne'

/-- A quantitative inverse bound on a fully specified positive compact patch.
The recovered ratio is C1 on the positive state quadrant, and compactness
provides its Lipschitz constant on the actual state image. -/
theorem incidenceState_inverse_bound {exponent shift parameterLower parameterUpper coordinateLower : ℝ}
    (hexponent : 1 < exponent) (hparameter : 0 < parameterLower)
    (hcoordinate : 0 < coordinateLower) :
    ∃ constant : ℝ≥0, ∀ left ∈ (Set.Icc parameterLower parameterUpper).prod
        ((Set.Icc coordinateLower 1).prod (Set.Icc coordinateLower 1)),
      ∀ right ∈ (Set.Icc parameterLower parameterUpper).prod
        ((Set.Icc coordinateLower 1).prod (Set.Icc coordinateLower 1)),
      left.2.1 ^ exponent + left.2.2 ^ exponent = 1 →
      right.2.1 ^ exponent + right.2.2 ^ exponent = 1 →
      dist left right ≤ constant *
        dist (incidenceState exponent shift left) (incidenceState exponent shift right) := by
  let patch : Set (ℝ × ℝ × ℝ) := (Set.Icc parameterLower parameterUpper).prod
    ((Set.Icc coordinateLower 1).prod (Set.Icc coordinateLower 1))
  have hpatch : IsCompact patch := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hstate : ContDiffOn ℝ 1 (incidenceState exponent shift) patch := by
    have hratio : ContDiffOn ℝ 1 (fun point : ℝ × ℝ × ℝ => point.2.1 / point.2.2) patch :=
      contDiffOn_snd.fst.div contDiffOn_snd.snd
        (fun point hpoint => (hcoordinate.trans_le hpoint.2.2.1).ne')
    exact contDiffOn_fst.prodMk
      ((contDiffOn_fst.rpow_const_of_ne
        (fun point hpoint => (hparameter.trans_le hpoint.1.1).ne')).mul
        (hratio.rpow_const_of_ne (fun point hpoint =>
          (div_pos (hcoordinate.trans_le hpoint.2.1.1)
            (hcoordinate.trans_le hpoint.2.2.1)).ne')))
  have himage : incidenceState exponent shift '' patch ⊆
      (Set.Ioi (0 : ℝ)).prod (Set.Ioi (0 : ℝ)) := by
    rintro state ⟨point, hpoint, rfl⟩
    exact ⟨hparameter.trans_le hpoint.1.1,
      mul_pos (Real.rpow_pos_of_pos (hparameter.trans_le hpoint.1.1) _)
        (Real.rpow_pos_of_pos (div_pos (hcoordinate.trans_le hpoint.2.1.1)
          (hcoordinate.trans_le hpoint.2.2.1)) _)⟩
  obtain ⟨ratioConstant, hratioConstant⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (hpatch.image_of_continuousOn hstate.continuousOn)
      (((recoveredCoordinateRatio_contDiffOn exponent shift).locallyLipschitzOn
        ((convex_Ioi (0 : ℝ)).prod (convex_Ioi (0 : ℝ)))).mono himage)
  refine ⟨⟨1 + (ratioConstant : ℝ) / coordinateLower, by positivity⟩, ?_⟩
  intro left hleft right hright hleftCurve hrightCurve
  have hratioBound := hratioConstant.dist_le_mul
    (incidenceState exponent shift left) (Set.mem_image_of_mem _ hleft)
    (incidenceState exponent shift right) (Set.mem_image_of_mem _ hright)
  rw [recoveredCoordinateRatio_incidenceState hexponent
      (hparameter.trans_le hleft.1.1) (hcoordinate.trans_le hleft.2.1.1)
      (hcoordinate.trans_le hleft.2.2.1),
    recoveredCoordinateRatio_incidenceState hexponent
      (hparameter.trans_le hright.1.1) (hcoordinate.trans_le hright.2.1.1)
      (hcoordinate.trans_le hright.2.2.1), Real.dist_eq] at hratioBound
  have hcoordinates := (positive_arc_ratio_inverse_bound (lt_trans zero_lt_one hexponent)
    hcoordinate hleft.2.1 hleft.2.2 hright.2.1 hright.2.2 hleftCurve hrightCurve).trans hratioBound
  have hsum : |left.2.1 - right.2.1| + |left.2.2 - right.2.2| ≤
      ((ratioConstant : ℝ) / coordinateLower) *
        dist (incidenceState exponent shift left) (incidenceState exponent shift right) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hcoordinate).2
    nlinarith [hcoordinates]
  have hparameterBound : |left.1 - right.1| ≤
      dist (incidenceState exponent shift left) (incidenceState exponent shift right) := by
    change |left.1 - right.1| ≤ max (dist left.1 right.1) _
    simpa only [Real.dist_eq] using le_max_left (dist left.1 right.1)
      (dist (incidenceState exponent shift left).2 (incidenceState exponent shift right).2)
  change max (dist left.1 right.1) (max (dist left.2.1 right.2.1) (dist left.2.2 right.2.2)) ≤
    (1 + (ratioConstant : ℝ) / coordinateLower) *
      dist (incidenceState exponent shift left) (incidenceState exponent shift right)
  simp only [Real.dist_eq, max_le_iff]
  have hdist := dist_nonneg (x := incidenceState exponent shift left)
    (y := incidenceState exponent shift right)
  have hnonnegative : 0 ≤ (ratioConstant : ℝ) / coordinateLower := by positivity
  have hproduct : 0 ≤ ((ratioConstant : ℝ) / coordinateLower) *
      dist (incidenceState exponent shift left) (incidenceState exponent shift right) :=
    mul_nonneg hnonnegative hdist
  constructor
  · nlinarith [hproduct]
  · constructor <;> nlinarith [abs_nonneg (left.2.1 - right.2.1), abs_nonneg (left.2.2 - right.2.2)]

end LambdaCantor.First.Roots
