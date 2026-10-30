import LambdaCantor.RationalPowers.LargeExponentGroupedCoverage

noncomputable section
namespace LambdaCantor.RationalPowers
open Integer

/-- Exact closed joins on one common integer grid select a finite cell for
every real normalized parameter. This theorem contains no phase oracle. -/
theorem largeExponent_finiteCoverageCheck_select (layer commonDenominator : ℕ)
    (rows : List FiniteCoverageRow)
    (checked : finiteCoverageCheck layer commonDenominator rows = true)
    (coefficient : ℝ) (coefficient_bounds : coefficient ∈ Set.Icc (1 : ℝ) 3) :
    ∃ row ∈ rows, row.cell.m = layer ∧
      (row.cell.lower : ℝ) ≤ row.cell.denominator*coefficient ∧
      row.cell.denominator*coefficient ≤ (row.cell.upper : ℝ) := by
  have data : 0 < commonDenominator ∧
      (∀ row ∈ rows, row.cell.m = layer ∧ 0 < row.multiplier ∧
        row.cell.denominator*row.multiplier = commonDenominator) ∧
      intervalCoverScan (finiteCoverageIntervals rows) commonDenominator (3*commonDenominator) = true ∧
      ∃ row ∈ rows, row.cell.lower*row.multiplier ≤ commonDenominator ∧
        commonDenominator ≤ row.cell.upper*row.multiplier := by
    simpa only [finiteCoverageCheck,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,
      decide_eq_true_eq,and_assoc] using checked
  obtain ⟨initial,initial_member,initial_lower,initial_upper⟩ := data.2.2.2
  have initially_covered : ∃ interval ∈ finiteCoverageIntervals rows,
      interval.1 ≤ (commonDenominator : ℤ) ∧ (commonDenominator : ℤ) ≤ interval.2 := by
    refine ⟨_,List.mem_map.mpr ⟨initial,initial_member,rfl⟩,?_,?_⟩
    · change ((initial.cell.lower*initial.multiplier : ℕ) : ℤ) ≤ (commonDenominator : ℤ)
      exact_mod_cast initial_lower
    · change (commonDenominator : ℤ) ≤ ((initial.cell.upper*initial.multiplier : ℕ) : ℤ)
      exact_mod_cast initial_upper
  have denominator_positive : (0 : ℝ) < commonDenominator := by exact_mod_cast data.1
  obtain ⟨interval,interval_member,lower,upper⟩ := closed_integer_cover_sound
    (finiteCoverageIntervals rows) commonDenominator (3*commonDenominator) data.2.2.1 initially_covered
    (commonDenominator*coefficient)
    (by norm_num; nlinarith [coefficient_bounds.1])
    (by norm_num; nlinarith [coefficient_bounds.2])
  obtain ⟨row,row_member,identity⟩ := List.mem_map.mp interval_member
  subst interval
  have row_data := data.2.1 row row_member
  have multiplier_positive : (0 : ℝ) < row.multiplier := by exact_mod_cast row_data.2.1
  have denominator_identity : (commonDenominator : ℝ) = row.cell.denominator*row.multiplier := by
    exact_mod_cast row_data.2.2.symm
  simp only [Int.cast_mul,Int.cast_natCast] at lower upper
  rw [denominator_identity] at lower upper
  refine ⟨row,row_member,row_data.1,?_,?_⟩
  · apply (mul_le_mul_iff_right₀ multiplier_positive).1
    nlinarith [lower]
  · apply (mul_le_mul_iff_right₀ multiplier_positive).1
    nlinarith [upper]

structure LargeExponentCoverageRow where
  interval : FiniteCoverageRow
  sources : Array TailPhaseGeometry
  arcs : List FinitePhaseArc

/-- Both the outer joins and every inner full-phase cell are executable
finite checks. Callers never need to provide a forall-real-parameter lemma. -/
def largeExponentFullLayerCheck (layer commonDenominator : ℕ)
    (rows : List LargeExponentCoverageRow) : Bool :=
  finiteCoverageCheck layer commonDenominator (rows.map LargeExponentCoverageRow.interval) &&
  rows.all (fun row => finitePhaseCellCheck row.interval.cell row.sources row.arcs)

theorem largeExponentFullLayerCheck_sound (layer commonDenominator : ℕ)
    (rows : List LargeExponentCoverageRow)
    (checked : largeExponentFullLayerCheck layer commonDenominator rows = true) :
    FiniteCoverageCertified layer := by
  have data :
      finiteCoverageCheck layer commonDenominator (rows.map LargeExponentCoverageRow.interval) = true ∧
      rows.all (fun row => finitePhaseCellCheck row.interval.cell row.sources row.arcs) = true := by
    simpa only [largeExponentFullLayerCheck,Bool.and_eq_true] using checked
  intro coefficient coefficient_bounds
  obtain ⟨interval,interval_member,layer_identity,lower,upper⟩ := largeExponent_finiteCoverageCheck_select
    layer commonDenominator (rows.map LargeExponentCoverageRow.interval) data.1 coefficient coefficient_bounds
  obtain ⟨row,row_member,identity⟩ := List.mem_map.mp interval_member
  subst interval
  exact ⟨row.interval.cell,row.sources,row.arcs,layer_identity,
    (List.all_eq_true.mp data.2) row row_member,lower,upper⟩

/-- Denominator-aware outer assembly. Each chosen row has its own single
fixed endpoint, and only that row's b-scaled phase checker may certify it. -/
def largeExponentGroupedLayerCheck (denominator layer commonDenominator : ℕ)
    (rows : List LargeExponentCoverageRow) : Bool :=
  finiteCoverageCheck layer commonDenominator (rows.map LargeExponentCoverageRow.interval) &&
  rows.all (fun row => largeExponentGroupedCellCheck denominator row.interval.cell row.sources row.arcs)

theorem largeExponentGroupedLayerCheck_sound (denominator layer commonDenominator : ℕ)
    (rows : List LargeExponentCoverageRow)
    (checked : largeExponentGroupedLayerCheck denominator layer commonDenominator rows = true) :
    LargeExponentGroupedCoverageChecked layer denominator := by
  have data :
      finiteCoverageCheck layer commonDenominator (rows.map LargeExponentCoverageRow.interval) = true ∧
      rows.all (fun row => largeExponentGroupedCellCheck denominator row.interval.cell row.sources row.arcs) = true := by
    simpa only [largeExponentGroupedLayerCheck,Bool.and_eq_true] using checked
  intro coefficient coefficient_bounds
  obtain ⟨interval,interval_member,layer_identity,lower,upper⟩ := largeExponent_finiteCoverageCheck_select
    layer commonDenominator (rows.map LargeExponentCoverageRow.interval) data.1 coefficient coefficient_bounds
  obtain ⟨row,row_member,identity⟩ := List.mem_map.mp interval_member
  subst interval
  exact ⟨row.interval.cell,row.sources,row.arcs,layer_identity,
    (List.all_eq_true.mp data.2) row row_member,lower,upper⟩

theorem largeExponent_full_layer_positive_dimension
    (layer commonDenominator : ℕ) (rows : List LargeExponentCoverageRow)
    (checked : largeExponentFullLayerCheck layer commonDenominator rows = true)
    (numerator denominator : ℕ) (denominator_positive : 0 < denominator)
    (coprime : numerator.Coprime denominator)
    (exponent_gt_one : 1 < (numerator : ℝ)/denominator)
    (exponent_ne_two : (numerator : ℝ)/denominator ≠ 2)
    (normalized : (((numerator : ℝ)/denominator)/(3 : ℝ)^layer) ∈ Set.Icc (1 : ℝ) 3) :
    0 < dimH (intersection ((numerator : ℝ)/denominator) (1/3)) :=
  largeExponent_normalized_finite_positive_dimension layer numerator denominator
    (largeExponentFullLayerCheck_sound layer commonDenominator rows checked)
    denominator_positive coprime exponent_gt_one exponent_ne_two normalized

theorem largeExponent_grouped_layer_positive_dimension
    (denominator layer commonDenominator : ℕ) (rows : List LargeExponentCoverageRow)
    (checked : largeExponentGroupedLayerCheck denominator layer commonDenominator rows = true)
    (numerator : ℕ) (denominator_positive : 0 < denominator)
    (coprime : numerator.Coprime denominator)
    (exponent_gt_one : 1 < (numerator : ℝ)/denominator)
    (exponent_ne_two : (numerator : ℝ)/denominator ≠ 2)
    (normalized : (((numerator : ℝ)/denominator)/(3 : ℝ)^layer) ∈ Set.Icc (1 : ℝ) 3) :
    0 < dimH (intersection ((numerator : ℝ)/denominator) (1/3)) :=
  largeExponent_normalized_grouped_positive_dimension layer numerator denominator
    (largeExponentGroupedLayerCheck_sound denominator layer commonDenominator rows checked)
    denominator_positive coprime exponent_gt_one exponent_ne_two normalized

structure LargeExponentLayerBundle where
  commonDenominator : ℕ
  rows : List LargeExponentCoverageRow

/-- One finite all-check covers exactly five grouped layers times 108
denominators and three full-phase layers. The two index offsets are checked
by the soundness proof, rather than supplied as a forall-real hypothesis. -/
def largeExponentAllFiniteLayersCheck
    (grouped : Fin 5 → Fin 108 → LargeExponentLayerBundle)
    (full : Fin 3 → LargeExponentLayerBundle) : Bool :=
  (List.finRange 5).all (fun layer => (List.finRange 108).all (fun denominator =>
    largeExponentGroupedLayerCheck (denominator.val+2) (layer.val+7)
      (grouped layer denominator).commonDenominator (grouped layer denominator).rows)) &&
  (List.finRange 3).all (fun layer => largeExponentFullLayerCheck (layer.val+12)
    (full layer).commonDenominator (full layer).rows)

/-- Final large-exponent assembly from finite decidable table acceptance and
the separately certified unbounded tail. There is no caller-written phase,
source, or forall-real-parameter coverage assumption. -/
theorem largeExponent_finite_table_positive_dimension
    (grouped : Fin 5 → Fin 108 → LargeExponentLayerBundle)
    (full : Fin 3 → LargeExponentLayerBundle)
    (checked : largeExponentAllFiniteLayersCheck grouped full = true)
    (tail : LargeExponentTailCoverageChecked) (numerator denominator : ℕ)
    (denominator_lower : 2 ≤ denominator) (denominator_upper : denominator ≤ 109)
    (coprime : numerator.Coprime denominator)
    (large : (2187 : ℝ) ≤ (numerator : ℝ)/denominator) :
    0 < dimH (intersection ((numerator : ℝ)/denominator) (1/3)) := by
  have data :
      (List.finRange 5).all (fun layer => (List.finRange 108).all (fun denominator =>
        largeExponentGroupedLayerCheck (denominator.val+2) (layer.val+7)
          (grouped layer denominator).commonDenominator (grouped layer denominator).rows)) = true ∧
      (List.finRange 3).all (fun layer => largeExponentFullLayerCheck (layer.val+12)
        (full layer).commonDenominator (full layer).rows) = true := by
    simpa only [largeExponentAllFiniteLayersCheck,Bool.and_eq_true] using checked
  apply largeExponent_positive_dimension _ _ tail numerator denominator
    denominator_lower denominator_upper coprime large
  · intro layer layer_lower layer_upper denominator denominator_lower denominator_upper
    let layer_index : Fin 5 := ⟨layer-7,by omega⟩
    let denominator_index : Fin 108 := ⟨denominator-2,by omega⟩
    have layer_checked := (List.all_eq_true.mp data.1) layer_index (by simp)
    have cell_checked := (List.all_eq_true.mp layer_checked) denominator_index (by simp)
    have coverage := largeExponentGroupedLayerCheck_sound (denominator_index.val+2) (layer_index.val+7)
      (grouped layer_index denominator_index).commonDenominator (grouped layer_index denominator_index).rows cell_checked
    simpa only [layer_index,denominator_index,Nat.sub_add_cancel layer_lower,
      Nat.sub_add_cancel denominator_lower] using coverage
  · intro layer layer_lower layer_upper
    let layer_index : Fin 3 := ⟨layer-12,by omega⟩
    have layer_checked := (List.all_eq_true.mp data.2) layer_index (by simp)
    have coverage := largeExponentFullLayerCheck_sound (layer_index.val+12)
      (full layer_index).commonDenominator (full layer_index).rows layer_checked
    simpa only [layer_index,Nat.sub_add_cancel layer_lower] using coverage

end LambdaCantor.RationalPowers
