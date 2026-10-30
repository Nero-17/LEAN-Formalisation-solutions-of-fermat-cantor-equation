import LambdaCantor.Integer.FinitePhaseChecker

namespace LambdaCantor.Integer

noncomputable def finitePhaseRealOffset (cell : FinitePhaseCell) (geometry : TailPhaseGeometry)
    (offset : ℕ) : ℝ :=
  (3 : ℝ)^cell.m*Real.log
    (((2*finitePhaseCenter cell*finitePhaseLength cell geometry+
      3^cell.height*finitePhaseLength cell geometry : ℕ) : ℝ)/
      (2*finitePhaseCenter cell*finitePhaseLength cell geometry+2*offset : ℕ))/Real.log 3

noncomputable def finiteSourceLower (cell : FinitePhaseCell) (coefficient : ℝ)
    (geometry : TailPhaseGeometry) : ℝ :=
  Real.log ((geometry.q : ℝ)/3^(cell.verticalDepth+1))/Real.log 3+
    coefficient*finitePhaseRealOffset cell geometry (geometry.a+1)

noncomputable def finiteSourceUpper (cell : FinitePhaseCell) (coefficient : ℝ)
    (geometry : TailPhaseGeometry) : ℝ :=
  Real.log (((geometry.q : ℝ)+1)/3^(cell.verticalDepth+1))/Real.log 3+
    coefficient*finitePhaseRealOffset cell geometry geometry.a

def FinitePhaseCacheEncloses (cache : TailPhaseCache) (cell : FinitePhaseCell)
    (geometry : TailPhaseGeometry) : Prop :=
  cache.qLog.Encloses (2^80) (Real.log ((geometry.q : ℝ)/3^(cell.verticalDepth+1))/Real.log 3) ∧
  cache.nextQLog.Encloses (2^80) (Real.log (((geometry.q : ℝ)+1)/3^(cell.verticalDepth+1))/Real.log 3) ∧
  cache.atOffset.Encloses (2^80) (finitePhaseRealOffset cell geometry geometry.a) ∧
  cache.atNextOffset.Encloses (2^80) (finitePhaseRealOffset cell geometry (geometry.a+1))

theorem finitePhaseCache_sound (cell : FinitePhaseCell) (geometry : TailPhaseGeometry)
    (checked : finitePhaseAnalyticChecked cell geometry) :
    FinitePhaseCacheEncloses (finitePhaseCache cell geometry) cell geometry := by
  have qLog := logRatioLatticeInterval_sound (2^256) (2^80) geometry.q
    (3^(cell.verticalDepth+1)) 80 checked.1
  have nextQLog := logRatioLatticeInterval_sound (2^256) (2^80) (geometry.q+1)
    (3^(cell.verticalDepth+1)) 80 checked.2.1
  have offset := logRatioLatticeInterval_sound (2^256) (2^80*3^cell.m) _ _ 12 checked.2.2.1
  have nextOffset := logRatioLatticeInterval_sound (2^256) (2^80*3^cell.m) _ _ 12 checked.2.2.2
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [finitePhaseCache,IntInterval.Encloses,Nat.cast_one,one_mul,
      Nat.cast_pow,Nat.cast_ofNat,mul_div_assoc] using qLog
  · simpa only [finitePhaseCache,IntInterval.Encloses,Nat.cast_one,one_mul,Nat.cast_add,
      Nat.cast_pow,Nat.cast_ofNat,mul_div_assoc] using nextQLog
  · simpa only [finitePhaseCache,finitePhaseOffsetInterval,finitePhaseRealOffset,
      IntInterval.Encloses,Nat.cast_one,one_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
      mul_div_assoc,mul_assoc] using offset
  · simpa only [finitePhaseCache,finitePhaseOffsetInterval,finitePhaseRealOffset,
      IntInterval.Encloses,Nat.cast_one,one_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
      mul_div_assoc,mul_assoc] using nextOffset
def finiteCoefficientLower (cell : FinitePhaseCell) (bounds : IntInterval) : ℤ :=
  (if 0 ≤ bounds.lower then (cell.lower : ℤ) else (cell.upper : ℤ))*bounds.lower

def finiteCoefficientUpper (cell : FinitePhaseCell) (bounds : IntInterval) : ℤ :=
  (if 0 ≤ bounds.upper then (cell.upper : ℤ) else (cell.lower : ℤ))*bounds.upper

theorem finiteCoefficient_bounds (cell : FinitePhaseCell) (coefficient value : ℝ) (bounds : IntInterval)
    (coefficientPositive : 0 ≤ coefficient)
    (coefficientLower : (cell.lower : ℝ) ≤ (cell.denominator : ℝ)*coefficient)
    (coefficientUpper : (cell.denominator : ℝ)*coefficient ≤ (cell.upper : ℝ))
    (enclosed : bounds.Encloses (2^80) value) :
    ((finiteCoefficientLower cell bounds : ℤ) : ℝ) ≤ (cell.denominator : ℝ)*(2^80 : ℝ)*(coefficient*value) ∧
      (cell.denominator : ℝ)*(2^80 : ℝ)*(coefficient*value) ≤ (finiteCoefficientUpper cell bounds : ℤ) := by
  have lowerProduct := mul_le_mul_of_nonneg_left enclosed.1
    (show 0 ≤ (cell.denominator : ℝ)*coefficient by positivity)
  have upperProduct := mul_le_mul_of_nonneg_left enclosed.2
    (show 0 ≤ (cell.denominator : ℝ)*coefficient by positivity)
  constructor
  · unfold finiteCoefficientLower
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
  · unfold finiteCoefficientUpper
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

theorem finitePhaseRow_sound (cell : FinitePhaseCell) (cache : TailPhaseCache) (arc : FinitePhaseArc)
    (geometry : TailPhaseGeometry) (coefficient : ℝ)
    (coefficientPositive : 0 ≤ coefficient)
    (coefficientLower : (cell.lower : ℝ) ≤ (cell.denominator : ℝ)*coefficient)
    (coefficientUpper : (cell.denominator : ℝ)*coefficient ≤ (cell.upper : ℝ))
    (denominatorPositive : 0 < cell.denominator)
    (enclosed : FinitePhaseCacheEncloses cache cell geometry) :
    finiteSourceLower cell coefficient geometry <
        ((finitePhaseRow cell cache arc).lower : ℝ)/((cell.denominator : ℝ)*2^80)+arc.shift ∧
      ((finitePhaseRow cell cache arc).upper : ℝ)/((cell.denominator : ℝ)*2^80)+arc.shift <
        finiteSourceUpper cell coefficient geometry := by
  have denominatorRealPositive : (0 : ℝ) < cell.denominator := by exact_mod_cast denominatorPositive
  have offset := (finiteCoefficient_bounds cell coefficient _ cache.atOffset coefficientPositive
    coefficientLower coefficientUpper enclosed.2.2.1).1
  have nextOffset := (finiteCoefficient_bounds cell coefficient _ cache.atNextOffset coefficientPositive
    coefficientLower coefficientUpper enclosed.2.2.2).2
  have insetPositive : (0 : ℝ) < finitePhaseInset cell := by
    have nonnegative : (0 : ℤ) ≤ (cell.denominator*2^80 : ℤ)/10^12 := Int.ediv_nonneg (by positivity) (by norm_num)
    exact_mod_cast (show (0 : ℤ) < finitePhaseInset cell by unfold finitePhaseInset; omega)
  have lowerClipped : finitePhaseLower cell cache-arc.shift*(cell.denominator*2^80) ≤
      (finitePhaseRow cell cache arc).lower := le_max_right _ _
  have upperClipped : (finitePhaseRow cell cache arc).upper ≤
      finitePhaseUpper cell cache-arc.shift*(cell.denominator*2^80) := min_le_right _ _
  have lowerClippedReal : (finitePhaseLower cell cache : ℝ)-(arc.shift : ℝ)*((cell.denominator : ℝ)*2^80) ≤
      (finitePhaseRow cell cache arc).lower := by exact_mod_cast lowerClipped
  have upperClippedReal : ((finitePhaseRow cell cache arc).upper : ℝ) ≤
      (finitePhaseUpper cell cache : ℝ)-(arc.shift : ℝ)*((cell.denominator : ℝ)*2^80) := by exact_mod_cast upperClipped
  have lowerIdentity : finitePhaseLower cell cache =
      (cell.denominator : ℤ)*cache.qLog.upper+finiteCoefficientUpper cell cache.atNextOffset+finitePhaseInset cell := rfl
  have upperIdentity : finitePhaseUpper cell cache =
      (cell.denominator : ℤ)*cache.nextQLog.lower+finiteCoefficientLower cell cache.atOffset-finitePhaseInset cell := rfl
  rw [lowerIdentity] at lowerClippedReal
  rw [upperIdentity] at upperClippedReal
  push_cast at lowerClippedReal upperClippedReal
  have qUpper := mul_le_mul_of_nonneg_left enclosed.1.2 denominatorRealPositive.le
  have nextQLower := mul_le_mul_of_nonneg_left enclosed.2.1.1 denominatorRealPositive.le
  norm_num only [Nat.cast_pow,Nat.cast_ofNat] at qUpper nextQLower
  constructor
  · have strict : (finiteSourceLower cell coefficient geometry-(arc.shift : ℝ))*((cell.denominator : ℝ)*2^80) <
        ((finitePhaseRow cell cache arc).lower : ℝ) := by
      unfold finiteSourceLower
      nlinarith
    have divided := (lt_div_iff₀ (by positivity : (0 : ℝ) < (cell.denominator : ℝ)*2^80)).2 strict
    linarith
  · have strict : ((finitePhaseRow cell cache arc).upper : ℝ) <
        (finiteSourceUpper cell coefficient geometry-(arc.shift : ℝ))*((cell.denominator : ℝ)*2^80) := by
      unfold finiteSourceUpper
      nlinarith
    have divided := (div_lt_iff₀ (by positivity : (0 : ℝ) < (cell.denominator : ℝ)*2^80)).2 strict
    linarith

theorem finitePhaseCellCheck_sound (cell : FinitePhaseCell) (sources : Array TailPhaseGeometry)
    (arcs : List FinitePhaseArc) (checked : finitePhaseCellCheck cell sources arcs = true)
    (coefficient phase : ℝ) (coefficientPositive : 0 ≤ coefficient)
    (coefficientLower : (cell.lower : ℝ) ≤ cell.denominator*coefficient)
    (coefficientUpper : cell.denominator*coefficient ≤ (cell.upper : ℝ))
    (phaseBounds : phase ∈ Set.Icc (0 : ℝ) 1) :
    ∃ geometry : TailPhaseGeometry, ∃ band : Fin 14, ∃ shift : ℤ,
      finitePhaseGeometryChecked cell geometry band ∧
      finiteSourceLower cell coefficient geometry < phase+shift ∧
      phase+shift < finiteSourceUpper cell coefficient geometry := by
  have data : cell.Checked ∧
      sources.all (fun geometry => decide (finitePhaseAnalyticChecked cell geometry)) = true ∧
      arcs.all (fun arc => decide (arc.sourceIndex < sources.size ∧
        finitePhaseGeometryChecked cell sources[arc.sourceIndex]! arc.band)) = true ∧
      phaseCoverCheck (cell.denominator*2^80) (arcs.map (fun arc =>
        finitePhaseRow cell (sources.map (finitePhaseCache cell))[arc.sourceIndex]! arc)) = true := by
    simpa only [finitePhaseCellCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using checked
  have denominatorPositive := data.1.2.2.2.1
  obtain ⟨row,rowMember,rowLower,rowUpper⟩ := phaseCoverCheck_row_sound (cell.denominator*2^80)
    (by positivity) _ data.2.2.2 phase phaseBounds
  obtain ⟨arc,arcMember,rfl⟩ := List.mem_map.mp rowMember
  have arcChecked := of_decide_eq_true ((List.all_eq_true.mp data.2.2.1) arc arcMember)
  have analytic : finitePhaseAnalyticChecked cell sources[arc.sourceIndex]! := by
    simpa only [getElem!_pos sources arc.sourceIndex arcChecked.1] using
      of_decide_eq_true ((Array.all_eq_true.mp data.2.1) arc.sourceIndex arcChecked.1)
  have cacheIdentity : (sources.map (finitePhaseCache cell))[arc.sourceIndex]! =
      finitePhaseCache cell sources[arc.sourceIndex]! := by
    simp only [getElem!_pos (sources.map (finitePhaseCache cell)) arc.sourceIndex
      (show arc.sourceIndex < (sources.map (finitePhaseCache cell)).size by
      simpa only [Array.size_map] using arcChecked.1),Array.getElem_map,
      getElem!_pos sources arc.sourceIndex arcChecked.1]
  have enclosed := finitePhaseCache_sound cell _ analytic
  have rowSound := finitePhaseRow_sound cell (finitePhaseCache cell sources[arc.sourceIndex]!) arc
    sources[arc.sourceIndex]! coefficient coefficientPositive coefficientLower coefficientUpper
    denominatorPositive enclosed
  rw [cacheIdentity] at rowLower rowUpper
  refine ⟨sources[arc.sourceIndex]!,arc.band,arc.shift,arcChecked.2,?_,?_⟩
  · norm_num only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at rowLower
    linarith [rowSound.1]
  · norm_num only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at rowUpper
    linarith [rowSound.2]

end LambdaCantor.Integer


