import LambdaCantor.Last.AnalyticCoarseCounting

noncomputable section
namespace LambdaCantor.Last

theorem coarse_consecutive_integer_arc_family
    {exponent normalizedHull arcLeft : ℝ}
    (hexponent : 1 ≤ exponent) (hhull : 0 ≤ normalizedHull) :
    ∃ indices : Finset ℤ,
      (indices.card : ℤ) = ⌊(exponent - 1) * normalizedHull⌋ ∧
      ∀ index ∈ indices,
        -exponent * normalizedHull ≤ arcLeft + (index : ℝ) ∧
          arcLeft + normalizedHull + (index : ℝ) < 0 := by
  classical
  have hfloor : (0 : ℤ) ≤ ⌊(exponent - 1) * normalizedHull⌋ :=
    Int.le_floor.mpr (by simpa using mul_nonneg (sub_nonneg.mpr hexponent) hhull)
  let count : ℕ := (⌊(exponent - 1) * normalizedHull⌋).toNat
  have hcount_int : (count : ℤ) = ⌊(exponent - 1) * normalizedHull⌋ :=
    Int.toNat_of_nonneg hfloor
  have hcount : (count : ℝ) ≤ (exponent - 1) * normalizedHull := by
    simpa only [← hcount_int, Int.cast_natCast] using
      Int.floor_le ((exponent - 1) * normalizedHull)
  obtain ⟨shift, hshift⟩ := coarse_consecutive_translates_inside_hull
    (arcLeft := arcLeft) count hcount
  have hinjective : Function.Injective
      (fun index : Fin count => shift + (index.val : ℤ)) := by
    intro first second hequal
    apply Fin.ext
    have hcast : (first.val : ℤ) = (second.val : ℤ) := add_left_cancel hequal
    exact_mod_cast hcast
  refine ⟨Finset.univ.image (fun index : Fin count => shift + (index.val : ℤ)), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinjective]
    simpa only [Finset.card_univ, Fintype.card_fin] using hcount_int
  · intro index hindex
    obtain ⟨original, _, rfl⟩ := Finset.mem_image.mp hindex
    simpa only [Int.cast_add, Int.cast_natCast, add_assoc] using hshift original

theorem coarse_three_gap_capacity_of_cover
    {firstRatio secondRatio thirdRatio exponent normalizedHull arcLeft : ℝ}
    {firstLeft firstRight secondLeft secondRight thirdLeft thirdRight : ℝ}
    (hhull : 0 < normalizedHull)
    (hfirst : firstRight - firstLeft ≤ firstRatio * exponent * normalizedHull)
    (hsecond : secondRight - secondLeft ≤ secondRatio * exponent * normalizedHull)
    (hthird : thirdRight - thirdLeft ≤ thirdRatio * exponent * normalizedHull)
    (indices : Finset ℤ)
    (hcover : ∀ index ∈ indices,
      (firstLeft ≤ arcLeft + (index : ℝ) ∧
        arcLeft + normalizedHull + (index : ℝ) ≤ firstRight) ∨
      (secondLeft ≤ arcLeft + (index : ℝ) ∧
        arcLeft + normalizedHull + (index : ℝ) ≤ secondRight) ∨
      (thirdLeft ≤ arcLeft + (index : ℝ) ∧
        arcLeft + normalizedHull + (index : ℝ) ≤ thirdRight)) :
    (indices.card : ℤ) ≤ coarseGapCapacity firstRatio exponent normalizedHull +
      coarseGapCapacity secondRatio exponent normalizedHull +
      coarseGapCapacity thirdRatio exponent normalizedHull := by
  classical
  let first : Finset ℤ := indices.filter (fun index : ℤ => firstLeft ≤ arcLeft + (index : ℝ) ∧
    arcLeft + normalizedHull + (index : ℝ) ≤ firstRight)
  let second : Finset ℤ := indices.filter (fun index : ℤ => secondLeft ≤ arcLeft + (index : ℝ) ∧
    arcLeft + normalizedHull + (index : ℝ) ≤ secondRight)
  let third : Finset ℤ := indices.filter (fun index : ℤ => thirdLeft ≤ arcLeft + (index : ℝ) ∧
    arcLeft + normalizedHull + (index : ℝ) ≤ thirdRight)
  have hsubset : indices ⊆ (first ∪ second) ∪ third := by
    intro index hindex
    rcases hcover index hindex with hfirst | hsecond | hthird
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hindex, hfirst⟩))
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hindex, hsecond⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hindex, hthird⟩)
  have hcard : indices.card ≤ first.card + second.card + third.card := by
    have hsubset_card := Finset.card_le_card hsubset
    have hpair_card := Finset.card_union_le first second
    have htotal_card := Finset.card_union_le (first ∪ second) third
    omega
  have hfirst_card := coarse_gap_capacity_of_actual_translates hhull hfirst first
    (by intro index hindex; exact (Finset.mem_filter.mp hindex).2)
  have hsecond_card := coarse_gap_capacity_of_actual_translates hhull hsecond second
    (by intro index hindex; exact (Finset.mem_filter.mp hindex).2)
  have hthird_card := coarse_gap_capacity_of_actual_translates hhull hthird third
    (by intro index hindex; exact (Finset.mem_filter.mp hindex).2)
  have hcard_int : (indices.card : ℤ) ≤
      (first.card : ℤ) + (second.card : ℤ) + (third.card : ℤ) := by exact_mod_cast hcard
  omega

end LambdaCantor.Last
