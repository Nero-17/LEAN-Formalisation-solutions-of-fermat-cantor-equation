import LambdaCantor.Last.AnalyticIsolatedAffineCore

noncomputable section
namespace LambdaCantor.Last

/-- Actual affine isolated-point classification in both open periodicity
phases. The proof starts from relative isolation in the actual Cantor fibre,
fills all closed child hulls, derives its actual exclusive tail address, and
proves eventual periodicity. No isolated-coordinate arithmetic is assumed. -/
theorem isolated_affine_address_in_parameterField {ratio slope level : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2) (slope_lower : 1 ≤ slope)
    (outer : 1-2*ratio < ratio*slope) (middle : (1-2*ratio)*slope < 1)
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope)
    (point : {value | value ∈ cantorDust ratio ∧ positiveLinearContinuous slope value = level})
    (isolated : IsOpen ({point} : Set {value | value ∈ cantorDust ratio ∧
      positiveLinearContinuous slope value = level}))
    (digits : ℕ → Bool × Bool) (address_point : point.val = pairedAddressTail ratio digits 0) :
    point.val.1 ∈ parameterField ratio ∧ point.val.2 ∈ parameterField ratio := by
  have less_one : ratio < 1 := by linarith
  have slope_nonnegative : 0 ≤ slope := by linarith
  have filled : ∀ word : List (Bool × Bool), ∀ digit : Bool × Bool,
      level ∈ Set.Icc
        (positiveLinearContinuous slope (wordMap ratio word (wordMap ratio [digit] 0)))
        (positiveLinearContinuous slope (wordMap ratio word (wordMap ratio [digit] (1,1)))) →
      ∃ tail ∈ cantorDust ratio,
        positiveLinearContinuous slope (wordMap ratio word (wordMap ratio [digit] tail)) = level := by
    intro word digit brackets
    obtain ⟨other, other_in_word, other_level⟩ := affine_closed_word_hull_filled
      positive less_half outer middle (word++[digit]) (by simpa [wordMap_append] using brackets)
    obtain ⟨tail, tail_mem, representation⟩ := other_in_word
    refine ⟨tail, tail_mem, ?_⟩
    rw [← wordMap_append, representation]
    exact other_level
  obtain ⟨cutoff, unique_child⟩ := isolated_fibre_unique_filled_child positive less_half
    (positiveLinearContinuous slope) level point isolated filled
  have point_representation : ∀ depth,
      wordMap ratio (pairedAddressPrefix digits depth)
        (wordMap ratio [digits depth] (pairedAddressTail ratio digits (depth+1))) = point.val := by
    intro depth
    rw [← pairedAddressTail_recurrence positive.le less_one digits depth]
    exact (pairedAddressPrefix_representation positive.le less_one digits depth).trans address_point.symm
  have normalized_unique : ∀ depth, cutoff ≤ depth → ∀ other : Bool × Bool,
      other ≠ digits depth → ¬ AffineChildClosed ratio slope
        (positiveLinearContinuous slope (pairedAddressTail ratio digits depth)) other := by
    intro depth depth_lower other different other_inside
    apply unique_child (pairedAddressPrefix digits depth) (by simpa [pairedAddressPrefix_length] using depth_lower)
      (digits depth) (pairedAddressTail ratio digits (depth+1))
      (pairedAddressTail_mem_dust ratio digits _) (point_representation depth) other different
    have parent_level : level = positiveLinearContinuous slope (wordMap ratio (pairedAddressPrefix digits depth) 0)+
        ratio^depth*positiveLinearContinuous slope (pairedAddressTail ratio digits depth) := by
      rw [← point.property.2, address_point,
        ← pairedAddressPrefix_representation positive.le less_one digits depth,
        positiveLinear_wordMap, pairedAddressPrefix_length]
    rw [positiveLinear_wordMap ratio slope (pairedAddressPrefix digits depth) (wordMap ratio [other] 0),
      positiveLinear_wordMap ratio slope (pairedAddressPrefix digits depth) (wordMap ratio [other] (1,1)),
      pairedAddressPrefix_length,
      (affine_child_endpoint_values ratio slope other).1,
      (affine_child_endpoint_values ratio slope other).2, parent_level]
    constructor
    · exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left other_inside.1 (pow_nonneg positive.le depth))
    · exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left other_inside.2 (pow_nonneg positive.le depth))
  have exclusive : ∀ depth, cutoff ≤ depth → AffineExclusiveRegion ratio slope
      (positiveLinearContinuous slope (pairedAddressTail ratio digits depth)) (digits depth) := by
    intro depth depth_lower
    apply affine_exclusive_of_unique_closed positive less_half slope_lower (digits depth)
    · rw [pairedAddressTail_recurrence positive.le less_one digits depth]
      exact affine_closed_child_bounds positive.le less_one slope_nonnegative _ (pairedAddressTail_mem_dust ratio digits _)
    · exact normalized_unique depth depth_lower
  have shifted_periodic : EventuallyPeriodicPairedAddress (fun depth => digits (depth+cutoff)) := by
    have shifted_recurrence : ∀ depth,
        positiveLinearContinuous slope (pairedAddressTail ratio digits (depth+cutoff)) =
          affineChildOffset ratio slope (digits (depth+cutoff))+ratio*
            positiveLinearContinuous slope (pairedAddressTail ratio digits ((depth+1)+cutoff)) := by
      intro depth
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        pairedAddressTail_affine_orbit positive.le less_one slope digits (depth+cutoff)
    rcases phase with small | mixed
    · exact small_phase_exclusive_address_periodic positive small _ _
        (fun depth => exclusive _ (by omega)) shifted_recurrence
    · exact mixed_phase_exclusive_address_periodic positive less_half mixed _ _
        (fun depth => exclusive _ (by omega)) shifted_recurrence
  obtain ⟨prefixLength, period, period_positive, periodic⟩ := shifted_periodic
  have periodic_original : EventuallyPeriodicPairedAddress digits := by
    refine ⟨cutoff+prefixLength, period, period_positive, ?_⟩
    intro index
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using periodic index
  have fields := paired_periodic_coordinates_in_parameterField positive.le less_one periodic_original
  simpa [address_point, pairedAddressTail] using fields

theorem isolated_affine_point_in_parameterField {ratio slope level : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2) (slope_lower : 1 ≤ slope)
    (outer : 1-2*ratio < ratio*slope) (middle : (1-2*ratio)*slope < 1)
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope)
    (point : {value | value ∈ cantorDust ratio ∧ positiveLinearContinuous slope value = level})
    (isolated : IsOpen ({point} : Set {value | value ∈ cantorDust ratio ∧
      positiveLinearContinuous slope value = level})) :
    point.val.1 ∈ parameterField ratio ∧ point.val.2 ∈ parameterField ratio := by
  obtain ⟨firstDigits, first_address⟩ := point.property.1.1
  obtain ⟨secondDigits, second_address⟩ := point.property.1.2
  apply isolated_affine_address_in_parameterField positive less_half slope_lower outer middle phase
    point isolated (fun index => (firstDigits index, secondDigits index))
  apply Prod.ext
  · simpa [pairedAddressTail] using first_address.symm
  · simpa [pairedAddressTail] using second_address.symm

end LambdaCantor.Last
