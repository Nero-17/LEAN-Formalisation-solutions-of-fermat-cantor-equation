import LambdaCantor.First.DustCover

noncomputable section
namespace LambdaCantor.First.PrefixSlopes

open Set MeasureTheory
open scoped ENNReal NNReal

/-- Actual active descendants of a parent obey the projection strip count
whenever secant slopes on the target are uniformly close to the chosen slope.
The latter hypothesis follows from the certified mean-value strip estimate
on any sufficiently small interval of a C1 graph. -/
theorem active_child_strip_count {ratio slope constant exponent : ℝ}
    (hratio : 0 < ratio) (hcontract : ratio < 1)
    (hball : ∀ center radius : ℝ, 0 < radius →
      projectedMeasure ratio slope (Metric.ball center radius) ≤
        ENNReal.ofReal (constant * radius ^ exponent))
    {target : Set (ℝ × ℝ)} {prefixLength block : ℕ}
    (hflat : ∀ left ∈ target, ∀ right ∈ target,
      |(left.2 - right.2) - slope * (left.1 - right.1)| ≤
        ratio ^ block * |left.1 - right.1|)
    (parent : Fin prefixLength → Bool × Bool)
    (hparent : parent ∈ activeWords ratio target prefixLength) :
    (((activeWords ratio target (prefixLength + block)).filter
      (fun word => wordParent word = parent)).card : ℝ≥0∞) * (1 / 4 : ℝ≥0∞) ^ block ≤
      ENNReal.ofReal (constant * ((|slope| + 3) * ratio ^ block) ^ exponent) := by
  classical
  obtain ⟨point, ⟨witness, hwitness, rfl⟩, hpoint⟩ :=
    (mem_activeWords ratio target parent).1 hparent
  have hcount := child_strip_count hratio hcontract (pow_nonneg hratio.le block) hball
    ((activeWords ratio target (prefixLength + block)).filter (fun word => wordParent word = parent))
    parent (fun word hword => (Finset.mem_filter.1 hword).2)
    (center := projectedAddress ratio slope (fun position => witness (prefixLength + position)))
  have hmeets : ∀ word ∈ (activeWords ratio target (prefixLength + block)).filter
      (fun word => wordParent word = parent), ∃ digits ∈ prefixCylinder word,
        |projectedAddress ratio slope (fun position => digits (prefixLength + position)) -
          projectedAddress ratio slope (fun position => witness (prefixLength + position))| ≤
            ratio ^ block := by
    intro word hword
    obtain ⟨hactive, hsameparent⟩ := Finset.mem_filter.1 hword
    obtain ⟨childpoint, ⟨digits, hdigits, rfl⟩, hchildpoint⟩ :=
      (mem_activeWords ratio target word).1 hactive
    have hdigitsParent : digits ∈ prefixCylinder parent := by
      rw [← hsameparent]
      exact prefixCylinder_parent hdigits
    refine ⟨digits, hdigits, rescaled_strip_of_parent hratio hcontract hdigitsParent hwitness ?_⟩
    have hhorizontal :
        |(addressPoint ratio digits).1 - (addressPoint ratio witness).1| ≤ ratio ^ prefixLength :=
      address_close_of_prefix hratio.le hcontract (fun position hposition =>
        congrArg Prod.fst ((hdigitsParent ⟨position, hposition⟩).trans
          (hwitness ⟨position, hposition⟩).symm))
    have hsecant := (hflat (addressPoint ratio digits) hchildpoint
      (addressPoint ratio witness) hpoint).trans
        (mul_le_mul_of_nonneg_left hhorizontal (pow_nonneg hratio.le block))
    have hequal : projectedAddress ratio slope digits - projectedAddress ratio slope witness =
        ((addressPoint ratio digits).2 - (addressPoint ratio witness).2) -
          slope * ((addressPoint ratio digits).1 - (addressPoint ratio witness).1) := by
      unfold projectedAddress addressPoint
      ring
    rw [hequal]
    simpa only [mul_comm (ratio ^ block) (ratio ^ prefixLength)] using hsecant
  have hradius : ratio ^ block + (|slope| + 2) * ratio ^ block =
      (|slope| + 3) * ratio ^ block := by ring
  simpa only [hradius] using hcount hmeets

end LambdaCantor.First.PrefixSlopes

