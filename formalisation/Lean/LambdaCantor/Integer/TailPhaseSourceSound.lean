import LambdaCantor.Integer.TailPhaseChecker

namespace LambdaCantor.Integer

noncomputable def tailPhaseRealOffset (Z : ℝ) (length a : ℕ) : ℝ :=
  Z*Real.log ((Z+27/2)/(Z+(a : ℝ)/length))/Real.log 3

noncomputable def tailSourceLower (Z coefficient : ℝ) (geometry : TailPhaseGeometry) : ℝ :=
  Real.log ((geometry.q : ℝ)/243)/Real.log 3+
    coefficient*tailPhaseRealOffset Z (tailPhaseLength geometry) (geometry.a+1)

noncomputable def tailSourceUpper (Z coefficient : ℝ) (geometry : TailPhaseGeometry) : ℝ :=
  Real.log (((geometry.q : ℝ)+1)/243)/Real.log 3+
    coefficient*tailPhaseRealOffset Z (tailPhaseLength geometry) geometry.a

def TailPhaseCache.Encloses (cache : TailPhaseCache) (Z : ℝ) (geometry : TailPhaseGeometry) : Prop :=
  cache.qLog.Encloses (2^80) (Real.log ((geometry.q : ℝ)/243)/Real.log 3) ∧
  cache.nextQLog.Encloses (2^80) (Real.log (((geometry.q : ℝ)+1)/243)/Real.log 3) ∧
  cache.atOffset.Encloses (2^80) (tailPhaseRealOffset Z (tailPhaseLength geometry) geometry.a) ∧
  cache.atNextOffset.Encloses (2^80) (tailPhaseRealOffset Z (tailPhaseLength geometry) (geometry.a+1))

theorem tailPhaseCache_sound (geometry : TailPhaseGeometry) (checked : geometry.AnalyticChecked)
    (Z : ℝ) (large : 1180980 ≤ Z) : (tailPhaseCache geometry).Encloses Z geometry := by
  have qLog := logRatioLatticeInterval_sound (2^256) (2^80) geometry.q 243 80 checked.1
  have nextQLog := logRatioLatticeInterval_sound (2^256) (2^80) (geometry.q+1) 243 80 checked.2.1
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [tailPhaseCache,IntInterval.Encloses,Nat.cast_one,Nat.cast_ofNat,
      one_mul,mul_div_assoc] using qLog
  · simpa only [tailPhaseCache,IntInterval.Encloses,Nat.cast_one,Nat.cast_ofNat,one_mul,Nat.cast_add,
      mul_div_assoc] using nextQLog
  · exact tailPhaseInterval_sound _ _ _ _ _ checked.2.2.1 Z large
  · exact tailPhaseInterval_sound _ _ _ _ _ checked.2.2.2 Z large

def cellCoefficientLower (cell : ℕ) (bounds : IntInterval) : ℤ :=
  (if 0 ≤ bounds.lower then 2*(cell : ℤ)-1 else 2*cell+1)*bounds.lower

def cellCoefficientUpper (cell : ℕ) (bounds : IntInterval) : ℤ :=
  (if 0 ≤ bounds.upper then 2*(cell : ℤ)+1 else 2*cell-1)*bounds.upper

theorem cellCoefficient_bounds (cell : ℕ) (coefficient value : ℝ) (bounds : IntInterval)
    (coefficientPositive : 0 ≤ coefficient)
    (coefficientLower : 2*(cell : ℝ)-1 ≤ 4000*coefficient)
    (coefficientUpper : 4000*coefficient ≤ 2*(cell : ℝ)+1)
    (enclosed : bounds.Encloses (2^80) value) :
    ((cellCoefficientLower cell bounds : ℤ) : ℝ) ≤ 4000*(2^80 : ℝ)*(coefficient*value) ∧
      4000*(2^80 : ℝ)*(coefficient*value) ≤ (cellCoefficientUpper cell bounds : ℤ) := by
  have lowerProduct := mul_le_mul_of_nonneg_left enclosed.1
    (show 0 ≤ 4000*coefficient by positivity)
  have upperProduct := mul_le_mul_of_nonneg_left enclosed.2
    (show 0 ≤ 4000*coefficient by positivity)
  constructor
  · unfold cellCoefficientLower
    split_ifs with sign
    · have signReal : (0 : ℝ) ≤ bounds.lower := by exact_mod_cast sign
      have product := mul_le_mul_of_nonneg_right coefficientLower signReal
      push_cast
      norm_num only [Nat.cast_pow,Nat.cast_ofNat] at lowerProduct
      nlinarith
    · have signReal : (bounds.lower : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge sign)
      have product := mul_le_mul_of_nonpos_right coefficientUpper signReal
      push_cast
      norm_num only [Nat.cast_pow,Nat.cast_ofNat] at lowerProduct
      nlinarith
  · unfold cellCoefficientUpper
    split_ifs with sign
    · have signReal : (0 : ℝ) ≤ bounds.upper := by exact_mod_cast sign
      have product := mul_le_mul_of_nonneg_right coefficientUpper signReal
      push_cast
      norm_num only [Nat.cast_pow,Nat.cast_ofNat] at upperProduct
      nlinarith
    · have signReal : (bounds.upper : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge sign)
      have product := mul_le_mul_of_nonpos_right coefficientLower signReal
      push_cast
      norm_num only [Nat.cast_pow,Nat.cast_ofNat] at upperProduct
      nlinarith

theorem tailPhaseRow_sound (cell : ℕ) (cache : TailPhaseCache) (arc : TailPhaseArc)
    (geometry : TailPhaseGeometry) (Z coefficient : ℝ)
    (coefficientPositive : 0 ≤ coefficient)
    (coefficientLower : 2*(cell : ℝ)-1 ≤ 4000*coefficient)
    (coefficientUpper : 4000*coefficient ≤ 2*(cell : ℝ)+1)
    (enclosed : cache.Encloses Z geometry) :
    tailSourceLower Z coefficient geometry <
        ((tailPhaseRow cell cache arc).lower : ℝ)/(4000*2^80)+arc.shift ∧
      ((tailPhaseRow cell cache arc).upper : ℝ)/(4000*2^80)+arc.shift <
        tailSourceUpper Z coefficient geometry := by
  have offset := (cellCoefficient_bounds cell coefficient _ cache.atOffset coefficientPositive
    coefficientLower coefficientUpper enclosed.2.2.1).1
  have nextOffset := (cellCoefficient_bounds cell coefficient _ cache.atNextOffset coefficientPositive
    coefficientLower coefficientUpper enclosed.2.2.2).2
  have insetPositive : (0 : ℝ) < tailPhaseInset := by norm_num [tailPhaseInset]
  have lowerClipped : tailPhaseLower cell cache-arc.shift*(4000*2^80) ≤
      (tailPhaseRow cell cache arc).lower := le_max_right _ _
  have upperClipped : (tailPhaseRow cell cache arc).upper ≤
      tailPhaseUpper cell cache-arc.shift*(4000*2^80) := min_le_right _ _
  have lowerClippedReal : (tailPhaseLower cell cache : ℝ)-(arc.shift : ℝ)*(4000*2^80) ≤
      (tailPhaseRow cell cache arc).lower := by exact_mod_cast lowerClipped
  have upperClippedReal : ((tailPhaseRow cell cache arc).upper : ℝ) ≤
      (tailPhaseUpper cell cache : ℝ)-(arc.shift : ℝ)*(4000*2^80) := by exact_mod_cast upperClipped
  have lowerIdentity : tailPhaseLower cell cache =
      4000*cache.qLog.upper+cellCoefficientUpper cell cache.atNextOffset+tailPhaseInset := rfl
  have upperIdentity : tailPhaseUpper cell cache =
      4000*cache.nextQLog.lower+cellCoefficientLower cell cache.atOffset-tailPhaseInset := rfl
  rw [lowerIdentity] at lowerClippedReal
  rw [upperIdentity] at upperClippedReal
  push_cast at lowerClippedReal upperClippedReal
  have qUpper := enclosed.1.2
  have nextQLower := enclosed.2.1.1
  norm_num only [Nat.cast_pow,Nat.cast_ofNat] at qUpper nextQLower
  constructor
  · have strict : (tailSourceLower Z coefficient geometry-(arc.shift : ℝ))*(4000*2^80) <
        ((tailPhaseRow cell cache arc).lower : ℝ) := by
      unfold tailSourceLower
      nlinarith
    have divided := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4000*2^80)).2 strict
    linarith
  · have strict : ((tailPhaseRow cell cache arc).upper : ℝ) <
        (tailSourceUpper Z coefficient geometry-(arc.shift : ℝ))*(4000*2^80) := by
      unfold tailSourceUpper
      nlinarith
    have divided := (div_lt_iff₀ (by positivity : (0 : ℝ) < 4000*2^80)).2 strict
    linarith

/-- Acceptance of the pure finite checker supplies an actual logarithmic source
for every real tail parameter and every phase; the source's slope-band geometry
is retained in the conclusion, not discarded after coverage checking. -/
theorem tailPhaseCellCheck_sound (sources : Array TailPhaseGeometry) (cell : ℕ)
    (arcs : List TailPhaseArc) (checked : tailPhaseCellCheck sources cell arcs = true)
    (Z coefficient phase : ℝ) (large : 1180980 ≤ Z)
    (coefficientPositive : 0 ≤ coefficient)
    (coefficientLower : 2*(cell : ℝ)-1 ≤ 4000*coefficient)
    (coefficientUpper : 4000*coefficient ≤ 2*(cell : ℝ)+1)
    (phaseBounds : phase ∈ Set.Icc (0 : ℝ) 1) :
    ∃ geometry : TailPhaseGeometry, ∃ band : Fin 4, ∃ shift : ℤ,
      geometry.Checked cell band ∧
      tailSourceLower Z coefficient geometry < phase+shift ∧
      phase+shift < tailSourceUpper Z coefficient geometry := by
  have data : sources.all (fun geometry => decide geometry.AnalyticChecked) = true ∧
      arcs.all (fun arc => decide (arc.sourceIndex < sources.size ∧
        (sources[arc.sourceIndex]!).Checked cell arc.band)) = true ∧
      phaseCoverCheck (4000*2^80) (arcs.map (fun arc =>
        tailPhaseRow cell (sources.map tailPhaseCache)[arc.sourceIndex]! arc)) = true := by
    simpa only [tailPhaseCellCheck,tailPhaseCellCoreCheck,Bool.and_eq_true,and_assoc] using checked
  obtain ⟨row,rowMember,rowLower,rowUpper⟩ := phaseCoverCheck_row_sound (4000*2^80)
    (by positivity) _ data.2.2 phase phaseBounds
  obtain ⟨arc,arcMember,rfl⟩ := List.mem_map.mp rowMember
  have arcChecked := of_decide_eq_true ((List.all_eq_true.mp data.2.1) arc arcMember)
  have analytic : (sources[arc.sourceIndex]!).AnalyticChecked := by
    simpa only [getElem!_pos sources arc.sourceIndex arcChecked.1] using
      of_decide_eq_true ((Array.all_eq_true.mp data.1) arc.sourceIndex arcChecked.1)
  have cacheIdentity : (sources.map tailPhaseCache)[arc.sourceIndex]! =
      tailPhaseCache sources[arc.sourceIndex]! := by
    simp only [getElem!_pos (sources.map tailPhaseCache) arc.sourceIndex
      (show arc.sourceIndex < (sources.map tailPhaseCache).size by
      simpa only [Array.size_map] using arcChecked.1),Array.getElem_map,
      getElem!_pos sources arc.sourceIndex arcChecked.1]
  have enclosed := tailPhaseCache_sound _ analytic Z large
  have rowSound := tailPhaseRow_sound cell (tailPhaseCache sources[arc.sourceIndex]!) arc
    sources[arc.sourceIndex]! Z coefficient coefficientPositive coefficientLower coefficientUpper enclosed
  rw [cacheIdentity] at rowLower rowUpper
  refine ⟨sources[arc.sourceIndex]!,arc.band,arc.shift,arcChecked.2,?_,?_⟩
  · norm_num only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at rowLower
    linarith [rowSound.1]
  · norm_num only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at rowUpper
    linarith [rowSound.2]

end LambdaCantor.Integer
