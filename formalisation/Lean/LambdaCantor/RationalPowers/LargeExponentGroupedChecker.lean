import LambdaCantor.RationalPowers.LargeExponentGroupedChecks
import LambdaCantor.RationalPowers.LargeExponentFiniteLayers

noncomputable section
namespace LambdaCantor.RationalPowers
open Integer

/-- Raw phase bounds before clipping, needed before multiplying by the actual
rational denominator. Clipping first would silently pool different rotations. -/
theorem largeExponent_finite_raw_phase_bounds (cell : FinitePhaseCell)
    (cache : TailPhaseCache) (geometry : TailPhaseGeometry) (coefficient : ℝ)
    (coefficient_nonnegative : 0 ≤ coefficient)
    (coefficient_lower : (cell.lower : ℝ) ≤ cell.denominator*coefficient)
    (coefficient_upper : cell.denominator*coefficient ≤ (cell.upper : ℝ))
    (denominator_positive : 0 < cell.denominator)
    (enclosed : FinitePhaseCacheEncloses cache cell geometry) :
    finiteSourceLower cell coefficient geometry*((cell.denominator : ℝ)*2^80) <
      (finitePhaseLower cell cache : ℝ) ∧
    (finitePhaseUpper cell cache : ℝ) <
      finiteSourceUpper cell coefficient geometry*((cell.denominator : ℝ)*2^80) := by
  have denominator_real_positive : (0 : ℝ) < cell.denominator := by exact_mod_cast denominator_positive
  have offset := (finiteCoefficient_bounds cell coefficient _ cache.atOffset coefficient_nonnegative
    coefficient_lower coefficient_upper enclosed.2.2.1).1
  have next_offset := (finiteCoefficient_bounds cell coefficient _ cache.atNextOffset coefficient_nonnegative
    coefficient_lower coefficient_upper enclosed.2.2.2).2
  have inset_positive : (0 : ℝ) < finitePhaseInset cell := by
    have nonnegative : (0 : ℤ) ≤ (cell.denominator*2^80 : ℤ)/10^12 :=
      Int.ediv_nonneg (by positivity) (by norm_num)
    exact_mod_cast (show (0 : ℤ) < finitePhaseInset cell by unfold finitePhaseInset; omega)
  have q_upper := mul_le_mul_of_nonneg_left enclosed.1.2 denominator_real_positive.le
  have next_q_lower := mul_le_mul_of_nonneg_left enclosed.2.1.1 denominator_real_positive.le
  norm_num only [Nat.cast_pow,Nat.cast_ofNat] at q_upper next_q_lower offset next_offset
  have lower_identity : finitePhaseLower cell cache =
      (cell.denominator : ℤ)*cache.qLog.upper+
        finiteCoefficientUpper cell cache.atNextOffset+finitePhaseInset cell := rfl
  have upper_identity : finitePhaseUpper cell cache =
      (cell.denominator : ℤ)*cache.nextQLog.lower+
        finiteCoefficientLower cell cache.atOffset-finitePhaseInset cell := rfl
  constructor
  · rw [lower_identity]
    unfold finiteSourceLower
    push_cast
    norm_num only [Nat.cast_pow,Nat.cast_ofNat]
    nlinarith
  · rw [upper_identity]
    unfold finiteSourceUpper
    push_cast
    norm_num only [Nat.cast_pow,Nat.cast_ofNat]
    nlinarith

theorem largeExponentGroupedBatchCheck_sound (cell : FinitePhaseCell)
    (sources : Array TailPhaseGeometry) (items : List LargeExponentGroupedBatchItem)
    (checked : largeExponentGroupedBatchCheck cell sources items = true) :
    ∀ item ∈ items, largeExponentGroupedCellCheck item.denominator cell sources item.arcs = true := by
  have data : cell.Checked ∧
      sources.all (fun geometry => decide (finitePhaseAnalyticChecked cell geometry)) = true ∧
      items.all (fun item => decide (0 < item.denominator) &&
        largeExponentGroupedCellCoreCheck item.denominator cell sources (sources.map (finitePhaseCache cell)) item.arcs) = true := by
    simpa only [largeExponentGroupedBatchCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using checked
  intro item membership
  have item_checked := (List.all_eq_true.mp data.2.2) item membership
  have item_data : 0 < item.denominator ∧
      largeExponentGroupedCellCoreCheck item.denominator cell sources (sources.map (finitePhaseCache cell)) item.arcs = true := by
    simpa only [Bool.and_eq_true,decide_eq_true_eq] using item_checked
  simpa only [largeExponentGroupedCellCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
    And.intro (And.intro (And.intro item_data.1 data.1) data.2.1) item_data.2

theorem largeExponentGroupedCellCheck_sound (denominator : ℕ) (cell : FinitePhaseCell)
    (sources : Array TailPhaseGeometry) (arcs : List FinitePhaseArc)
    (checked : largeExponentGroupedCellCheck denominator cell sources arcs = true)
    (coefficient phase : ℝ) (coefficient_nonnegative : 0 ≤ coefficient)
    (coefficient_lower : (cell.lower : ℝ) ≤ cell.denominator*coefficient)
    (coefficient_upper : cell.denominator*coefficient ≤ (cell.upper : ℝ))
    (phase_bounds : phase ∈ Set.Icc (0 : ℝ) 1) :
    ∃ geometry : TailPhaseGeometry, ∃ band : Fin 14, ∃ shift : ℤ,
      finitePhaseGeometryChecked cell geometry band ∧
      (denominator : ℝ)*finiteSourceLower cell coefficient geometry < phase+shift ∧
      phase+shift < (denominator : ℝ)*finiteSourceUpper cell coefficient geometry := by
  have data : (0 < denominator ∧ cell.Checked) ∧
      sources.all (fun geometry => decide (finitePhaseAnalyticChecked cell geometry)) = true ∧
      arcs.all (fun arc => decide (arc.sourceIndex < sources.size ∧
        finitePhaseGeometryChecked cell sources[arc.sourceIndex]! arc.band)) = true ∧
      phaseCoverCheck (cell.denominator*2^80) (arcs.map (fun arc =>
        largeExponentGroupedPhaseRow denominator cell (sources.map (finitePhaseCache cell))[arc.sourceIndex]! arc)) = true := by
    simpa only [largeExponentGroupedCellCheck,largeExponentGroupedCellCoreCheck,
      Bool.and_eq_true,decide_eq_true_eq,and_assoc] using checked
  have denominator_real_positive : (0 : ℝ) < denominator := by exact_mod_cast data.1.1
  have scale_positive : (0 : ℝ) < (cell.denominator : ℝ)*2^80 := by
    have positive := data.1.2.2.2.2.1
    positivity
  obtain ⟨row,row_member,row_lower,row_upper⟩ := phaseCoverCheck_row_sound
    (cell.denominator*2^80) (by have positive := data.1.2.2.2.2.1; positivity) _ data.2.2.2 phase phase_bounds
  obtain ⟨arc,arc_member,rfl⟩ := List.mem_map.mp row_member
  have arc_checked := of_decide_eq_true ((List.all_eq_true.mp data.2.2.1) arc arc_member)
  have analytic : finitePhaseAnalyticChecked cell sources[arc.sourceIndex]! := by
    simpa only [getElem!_pos sources arc.sourceIndex arc_checked.1] using
      of_decide_eq_true ((Array.all_eq_true.mp data.2.1) arc.sourceIndex arc_checked.1)
  have cache_identity : (sources.map (finitePhaseCache cell))[arc.sourceIndex]! =
      finitePhaseCache cell (sources[arc.sourceIndex]!) := by
    simp only [getElem!_pos (sources.map (finitePhaseCache cell)) arc.sourceIndex (show arc.sourceIndex < (sources.map (finitePhaseCache cell)).size by
      simpa only [Array.size_map] using arc_checked.1),Array.getElem_map,
      getElem!_pos sources arc.sourceIndex arc_checked.1]
  rw [cache_identity] at row_lower row_upper
  have raw := largeExponent_finite_raw_phase_bounds cell _ sources[arc.sourceIndex]! coefficient
    coefficient_nonnegative coefficient_lower coefficient_upper data.1.2.2.2.2.1
    (finitePhaseCache_sound cell _ analytic)
  have lower_scaled := mul_lt_mul_of_pos_left raw.1 denominator_real_positive
  have upper_scaled := mul_lt_mul_of_pos_left raw.2 denominator_real_positive
  have clipped_lower : (denominator : ℤ)*finitePhaseLower cell (finitePhaseCache cell sources[arc.sourceIndex]!)-
      arc.shift*(cell.denominator*2^80) ≤
      (largeExponentGroupedPhaseRow denominator cell (finitePhaseCache cell sources[arc.sourceIndex]!) arc).lower :=
    le_max_right _ _
  have clipped_upper :
      (largeExponentGroupedPhaseRow denominator cell (finitePhaseCache cell sources[arc.sourceIndex]!) arc).upper ≤
      (denominator : ℤ)*finitePhaseUpper cell (finitePhaseCache cell sources[arc.sourceIndex]!)-
        arc.shift*(cell.denominator*2^80) := min_le_right _ _
  have clipped_lower_real :
      (denominator : ℝ)*(finitePhaseLower cell (finitePhaseCache cell sources[arc.sourceIndex]!) : ℝ)-
        (arc.shift : ℝ)*((cell.denominator : ℝ)*2^80) ≤
      (largeExponentGroupedPhaseRow denominator cell (finitePhaseCache cell sources[arc.sourceIndex]!) arc).lower := by
    exact_mod_cast clipped_lower
  have clipped_upper_real :
      ((largeExponentGroupedPhaseRow denominator cell (finitePhaseCache cell sources[arc.sourceIndex]!) arc).upper : ℝ) ≤
      (denominator : ℝ)*(finitePhaseUpper cell (finitePhaseCache cell sources[arc.sourceIndex]!) : ℝ)-
        (arc.shift : ℝ)*((cell.denominator : ℝ)*2^80) := by
    exact_mod_cast clipped_upper
  norm_num only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at row_lower row_upper scale_positive lower_scaled upper_scaled clipped_lower_real clipped_upper_real
  have phase_lower := (div_le_iff₀ scale_positive).1 row_lower
  have phase_upper := (le_div_iff₀ scale_positive).1 row_upper
  refine ⟨sources[arc.sourceIndex]!,arc.band,arc.shift,arc_checked.2,?_,?_⟩
  · apply (mul_lt_mul_iff_right₀ scale_positive).1
    nlinarith
  · apply (mul_lt_mul_iff_right₀ scale_positive).1
    nlinarith

/-- The b-aware finite checker feeds the rational phase transfer while the
center stays fixed to the cell's one legal endpoint throughout the proof. -/
theorem largeExponent_grouped_cell_log_source (denominator : ℕ) (cell : FinitePhaseCell)
    (sources : Array TailPhaseGeometry) (arcs : List FinitePhaseArc)
    (checked : largeExponentGroupedCellCheck denominator cell sources arcs = true)
    (exponent : ℝ) (exponent_positive : 0 < exponent)
    (coefficient_lower : (cell.lower : ℝ) ≤ cell.denominator*(exponent/3^cell.m))
    (coefficient_upper : cell.denominator*(exponent/3^cell.m) ≤ (cell.upper : ℝ)) :
    ∃ source : LogSourceData, ∃ phaseNumerator : ℤ,
      LargeExponentGeometryChecked exponent source ∧
      ((phaseNumerator : ℝ)/denominator)*Real.log 3+
        exponent*Real.log ((source.P : ℝ)/3^source.p)-Real.log exponent-
          Real.log ((source.Q+1 : ℝ)/3^source.q) < 0 ∧
      0 < ((phaseNumerator : ℝ)/denominator)*Real.log 3+
        exponent*Real.log ((source.P+1 : ℝ)/3^source.p)-Real.log exponent-
          Real.log ((source.Q : ℝ)/3^source.q) := by
  have data : 0 < denominator ∧ cell.Checked := by
    have conjunction := checked
    simp only [largeExponentGroupedCellCheck,largeExponentGroupedCellCoreCheck,
      Bool.and_eq_true,decide_eq_true_eq,and_assoc] at conjunction
    exact ⟨conjunction.1,conjunction.2.1⟩
  have base_positive : 0 < finiteCylinderBase cell := by
    unfold finiteCylinderBase
    have endpoint_positive := data.2.2.1
    positivity
  apply largeExponent_lattice_phase_cover_log_source exponent
    (((finiteCylinderBase cell : ℝ)+1/2)/3^(cell.m-cell.height)) denominator data.1 (by positivity)
  intro phase phase_bounds
  obtain ⟨geometry,band,shift,geometry_checked,lower,upper⟩ := largeExponentGroupedCellCheck_sound
    denominator cell sources arcs checked (exponent/3^cell.m) phase (by positivity)
    coefficient_lower coefficient_upper phase_bounds
  have identities := largeExponent_finite_centered_identities cell geometry band exponent data.2 geometry_checked.1
  refine ⟨finiteCylinderSource cell geometry band,shift,
    largeExponent_finite_geometry cell geometry band exponent data.2 geometry_checked
      coefficient_lower coefficient_upper,?_,?_⟩
  · rwa [identities.1] at lower
  · rwa [identities.2] at upper

end LambdaCantor.RationalPowers
