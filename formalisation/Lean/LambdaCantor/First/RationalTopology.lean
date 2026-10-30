import Mathlib.Data.Rat.Floor
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter Topology
namespace LambdaCantor.First

/-- Bounded numerators and denominators form a finite set of rationals. -/
theorem finite_bounded_rationals (bound denominatorBound : ℕ) :
    {q : ℚ | |(q : ℝ)| ≤ bound ∧ q.den ≤ denominatorBound}.Finite := by
  apply (((Set.finite_Icc (-(bound * denominatorBound : ℤ))
      (bound * denominatorBound : ℤ)).prod
      (Set.finite_Icc (0 : ℕ) denominatorBound)).image
      (fun pair : ℤ × ℕ => (pair.1 : ℚ) / pair.2)).subset
  intro q hq
  refine ⟨(q.num, q.den), ⟨?_, ⟨Nat.zero_le _, hq.2⟩⟩, ?_⟩
  · have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hcast : (q.num : ℝ) = (q : ℝ) * q.den := by
      rw [Rat.cast_def]
      field_simp
    have hb : (q.den : ℝ) ≤ denominatorBound := by exact_mod_cast hq.2
    have habs : |(q.num : ℝ)| ≤ (bound : ℝ) * denominatorBound := by
      rw [hcast, abs_mul, abs_of_pos hden]
      exact (mul_le_mul_of_nonneg_right hq.1 hden.le).trans
        (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
    have ⟨hlo, hhi⟩ := abs_le.mp habs
    constructor
    · exact_mod_cast hlo
    · exact_mod_cast hhi
  · exact q.num_div_den

/-- Every finite real set is avoided by a sufficiently small punctured ball. -/
theorem finite_punctured_avoidance (points : Set ℝ) (hpoints : points.Finite)
    (center : ℝ) : ∃ radius > 0, ∀ point ∈ points,
      point ≠ center → radius ≤ |point - center| := by
  classical
  induction points, hpoints using Set.Finite.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert point points hnot hfinite hind =>
    obtain ⟨radius, hpos, hbound⟩ := hind
    by_cases heq : point = center
    · refine ⟨radius, hpos, ?_⟩
      intro y hy hne
      rcases hy with rfl | hy
      · exact (hne heq).elim
      · exact hbound y hy hne
    · refine ⟨min radius |point - center|,
        lt_min hpos (abs_pos.mpr (sub_ne_zero.mpr heq)), ?_⟩
      intro y hy hne
      rcases hy with rfl | hy
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbound y hy hne)

/-- Denominators of rational points in a punctured neighborhood exceed any
prescribed bound. This includes rational as well as irrational centers. -/
theorem rational_denominators_escape (center : ℝ) (denominatorBound : ℕ) :
    ∃ radius > 0, ∀ q : ℚ, (q : ℝ) ≠ center →
      |(q : ℝ) - center| < radius → denominatorBound < q.den := by
  obtain ⟨bound, hbound⟩ := exists_nat_gt (|center| + 1)
  obtain ⟨radius, hpos, havoid⟩ := finite_punctured_avoidance
    ((fun q : ℚ => (q : ℝ)) ''
      {q : ℚ | |(q : ℝ)| ≤ bound ∧ q.den ≤ denominatorBound})
    ((finite_bounded_rationals bound denominatorBound).image _) center
  refine ⟨min radius 1, lt_min hpos (by norm_num), ?_⟩
  intro q hne hnear
  by_contra hden
  have habs : |(q : ℝ)| ≤ bound := by
    have htriangle := abs_add_le ((q : ℝ) - center) center
    have hnearOne := hnear.trans_le (min_le_right radius 1)
    have hsum : (q : ℝ) - center + center = (q : ℝ) := by ring
    rw [hsum] at htriangle
    linarith
  have hfar := havoid (q : ℝ) ⟨q, ⟨habs, by omega⟩, rfl⟩ hne
  have := hnear.trans_le (min_le_left radius 1)
  linarith

end LambdaCantor.First




