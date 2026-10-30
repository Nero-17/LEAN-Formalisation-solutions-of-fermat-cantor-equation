import LambdaCantor.Integer.FiniteCoverageChecks
import LambdaCantor.Integer.FiniteIntegerTransfer

namespace LambdaCantor.Integer

theorem finiteCoverageCheck_sound (m denominator : ℕ) (rows : List FiniteCoverageRow)
    (checked : finiteCoverageCheck m denominator rows = true)
    (cells : ∀ row ∈ rows, ∃ sources : Array TailPhaseGeometry,
      ∃ arcs : List FinitePhaseArc, finitePhaseCellCheck row.cell sources arcs = true) :
    FiniteCoverageCertified m := by
  have data : 0 < denominator ∧
      (∀ row ∈ rows, row.cell.m = m ∧ 0 < row.multiplier ∧
        row.cell.denominator*row.multiplier = denominator) ∧
      intervalCoverScan (finiteCoverageIntervals rows) denominator (3*denominator) = true ∧
      ∃ row ∈ rows, row.cell.lower*row.multiplier ≤ denominator ∧
        denominator ≤ row.cell.upper*row.multiplier := by
    simpa only [finiteCoverageCheck,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,
      decide_eq_true_eq,and_assoc] using checked
  obtain ⟨initial,initialMember,initialLower,initialUpper⟩ := data.2.2.2
  have initialCovered : ∃ interval ∈ finiteCoverageIntervals rows,
      interval.1 ≤ (denominator : ℤ) ∧ (denominator : ℤ) ≤ interval.2 := by
    refine ⟨_,List.mem_map.mpr ⟨initial,initialMember,rfl⟩,?_,?_⟩
    · change ((initial.cell.lower*initial.multiplier : ℕ) : ℤ) ≤ (denominator : ℤ)
      exact_mod_cast initialLower
    · change (denominator : ℤ) ≤ ((initial.cell.upper*initial.multiplier : ℕ) : ℤ)
      exact_mod_cast initialUpper
  intro coefficient coefficientBounds
  have denominatorPositive : (0 : ℝ) < denominator := by exact_mod_cast data.1
  obtain ⟨interval,member,lower,upper⟩ := closed_integer_cover_sound
    (finiteCoverageIntervals rows) denominator (3*denominator) data.2.2.1 initialCovered
    (denominator*coefficient) (by norm_num; nlinarith [coefficientBounds.1])
    (by norm_num; nlinarith [coefficientBounds.2])
  obtain ⟨row,rowMember,identity⟩ := List.mem_map.mp member
  subst interval
  have rowData := data.2.1 row rowMember
  obtain ⟨sources,arcs,cellChecked⟩ := cells row rowMember
  have multiplierPositive : (0 : ℝ) < row.multiplier := by exact_mod_cast rowData.2.1
  have denominatorIdentity : (denominator : ℝ) = row.cell.denominator*row.multiplier := by
    exact_mod_cast rowData.2.2.symm
  simp only [Int.cast_mul,Int.cast_natCast] at lower upper
  rw [denominatorIdentity] at lower upper
  refine ⟨row.cell,sources,arcs,rowData.1,cellChecked,?_,?_⟩
  · apply (mul_le_mul_iff_right₀ multiplierPositive).1
    nlinarith [lower]
  · apply (mul_le_mul_iff_right₀ multiplierPositive).1
    nlinarith [upper]

end LambdaCantor.Integer
