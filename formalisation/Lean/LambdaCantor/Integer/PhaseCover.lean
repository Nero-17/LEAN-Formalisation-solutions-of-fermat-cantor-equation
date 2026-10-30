import LambdaCantor.Integer.IntervalCertificate

namespace LambdaCantor.Integer

structure PhaseCoverRow where
  sourceIndex : ℕ
  lower : ℤ
  upper : ℤ
  shift : ℤ
  deriving DecidableEq

def phaseCoverCheck (denominator : ℕ) (rows : List PhaseCoverRow) : Bool :=
  intervalCoverScan (rows.map (fun row => (row.lower,row.upper))) 0 denominator &&
    rows.any (fun row => decide (row.lower ≤ 0 ∧ 0 ≤ row.upper))

theorem phaseCoverCheck_row_sound (denominator : ℕ) (positive : 0 < denominator)
    (rows : List PhaseCoverRow) (checked : phaseCoverCheck denominator rows = true)
    (phase : ℝ) (phaseBounds : phase ∈ Set.Icc (0 : ℝ) 1) :
    ∃ row ∈ rows, (row.lower : ℝ)/denominator ≤ phase ∧ phase ≤ (row.upper : ℝ)/denominator := by
  simp only [phaseCoverCheck,Bool.and_eq_true,List.any_eq_true,decide_eq_true_eq] at checked
  obtain ⟨scan,initialRow,initialMember,initialLower,initialUpper⟩ := checked
  have initialCovered : ∃ interval ∈ rows.map (fun row => (row.lower,row.upper)),
      interval.1 ≤ (0 : ℤ) ∧ 0 ≤ interval.2 :=
    ⟨(initialRow.lower,initialRow.upper),List.mem_map.mpr ⟨initialRow,initialMember,rfl⟩,
      initialLower,initialUpper⟩
  have denominatorPositive : (0 : ℝ) < denominator := by exact_mod_cast positive
  have scaledUpper : phase*(denominator : ℝ) ≤ denominator := by
    nlinarith [phaseBounds.2]
  obtain ⟨interval,intervalMember,lower,upper⟩ := closed_integer_cover_sound _ 0 denominator
    scan initialCovered (phase*denominator)
    (by simpa using mul_nonneg phaseBounds.1 denominatorPositive.le)
    (by simpa only [Int.cast_natCast] using scaledUpper)
  obtain ⟨row,member,identity⟩ := List.mem_map.mp intervalMember
  subst interval
  exact ⟨row,member,(div_le_iff₀ denominatorPositive).2 lower,
    (le_div_iff₀ denominatorPositive).2 upper⟩

/-- Integer overlap checking covers the circle, while each row's separate
strict analytic enclosure supplies a real source interval and integer rotation.
Clipping at 0 or 1 is harmless because the analytic bounds include a strict inset. -/
theorem phaseCoverCheck_sound (denominator : ℕ) (positive : 0 < denominator)
    (rows : List PhaseCoverRow) (checked : phaseCoverCheck denominator rows = true)
    (lowerPhase upperPhase : ℕ → ℝ)
    (enclosed : ∀ row ∈ rows,
      lowerPhase row.sourceIndex < (row.lower : ℝ)/denominator+row.shift ∧
      (row.upper : ℝ)/denominator+row.shift < upperPhase row.sourceIndex) :
    ∀ phase ∈ Set.Icc (0 : ℝ) 1, ∃ sourceIndex : ℕ, ∃ shift : ℤ,
      lowerPhase sourceIndex < phase+shift ∧ phase+shift < upperPhase sourceIndex := by
  simp only [phaseCoverCheck,Bool.and_eq_true,List.any_eq_true,decide_eq_true_eq] at checked
  obtain ⟨scan,initialRow,initialMember,initialLower,initialUpper⟩ := checked
  have initialCovered : ∃ interval ∈ rows.map (fun row => (row.lower,row.upper)),
      interval.1 ≤ (0 : ℤ) ∧ 0 ≤ interval.2 :=
    ⟨(initialRow.lower,initialRow.upper),List.mem_map.mpr ⟨initialRow,initialMember,rfl⟩,
      initialLower,initialUpper⟩
  intro phase phaseBounds
  have denominatorPositive : (0 : ℝ) < denominator := by exact_mod_cast positive
  have scaledLower : (0 : ℝ) ≤ phase*denominator := mul_nonneg phaseBounds.1 denominatorPositive.le
  have scaledUpper : phase*(denominator : ℝ) ≤ denominator := by
    nlinarith [phaseBounds.2]
  obtain ⟨interval,intervalMember,intervalLower,intervalUpper⟩ :=
    closed_integer_cover_sound _ 0 denominator scan initialCovered
      (phase*denominator) (by simpa using scaledLower) (by simpa using scaledUpper)
  obtain ⟨row,rowMember,identity⟩ := List.mem_map.mp intervalMember
  subst interval
  have rowEnclosed := enclosed row rowMember
  refine ⟨row.sourceIndex,row.shift,?_,?_⟩
  · have bound : (row.lower : ℝ)/denominator ≤ phase :=
      (div_le_iff₀ denominatorPositive).2 intervalLower
    linarith [rowEnclosed.1]
  · have bound : phase ≤ (row.upper : ℝ)/denominator :=
      (le_div_iff₀ denominatorPositive).2 intervalUpper
    linarith [rowEnclosed.2]

end LambdaCantor.Integer
