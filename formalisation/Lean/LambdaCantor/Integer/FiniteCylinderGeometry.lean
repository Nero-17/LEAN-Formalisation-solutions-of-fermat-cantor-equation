import LambdaCantor.Integer.FinitePhaseSourceSound
import LambdaCantor.Integer.PrefixConcatenation
import LambdaCantor.Integer.LogGeometry
import Mathlib.Data.Fintype.Fin

namespace LambdaCantor.Integer

def finiteLogBand (band : Fin 14) : Fin 10 :=
  match band.val with
  | 0 => 0 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 3 | 6 => 4
  | 7 => 5 | 8 => 7 | 9 => 5 | 10 => 6 | 11 => 7 | 12 => 8 | _ => 9
theorem finiteLogBand_inclusion (band : Fin 14) :
    ((logSourceBand (finiteLogBand band)).1 : ℝ)/(logSourceBand (finiteLogBand band)).2.1 ≤
      ((finitePhaseBand band).1 : ℝ)/(finitePhaseBand band).2.1 ∧
    ((finitePhaseBand band).2.2.1 : ℝ)/(finitePhaseBand band).2.2.2 ≤
      ((logSourceBand (finiteLogBand band)).2.2.1 : ℝ)/(logSourceBand (finiteLogBand band)).2.2.2 := by
  fin_cases band
  · change (89 : ℝ)/73 ≤ 11/9 ∧ (2027 : ℝ)/1624 ≤ 171/137
    norm_num
  · change (89 : ℝ)/57 ≤ 11/7 ∧ (21 : ℝ)/11 ≤ 171/89
    norm_num
  · change (89 : ℝ)/73 ≤ 89/73 ∧ (171 : ℝ)/137 ≤ 171/137
    norm_num
  · change (101 : ℝ)/79 ≤ 101/79 ∧ (183 : ℝ)/143 ≤ 183/143
    norm_num
  · change (89 : ℝ)/57 ≤ 89/57 ∧ (171 : ℝ)/89 ≤ 171/89
    norm_num
  · change (143 : ℝ)/61 ≤ 143/61 ∧ (237 : ℝ)/101 ≤ 237/101
    norm_num
  · change (137 : ℝ)/57 ≤ 137/57 ∧ (219 : ℝ)/89 ≤ 219/89
    norm_num
  · change (137 : ℝ)/171 ≤ 1624/2027 ∧ (9 : ℝ)/11 ≤ 73/89
    norm_num
  · change (89 : ℝ)/171 ≤ 11/21 ∧ (7 : ℝ)/11 ≤ 57/89
    norm_num
  · change (137 : ℝ)/171 ≤ 137/171 ∧ (73 : ℝ)/89 ≤ 73/89
    norm_num
  · change (143 : ℝ)/183 ≤ 143/183 ∧ (79 : ℝ)/101 ≤ 79/101
    norm_num
  · change (89 : ℝ)/171 ≤ 89/171 ∧ (57 : ℝ)/89 ≤ 57/89
    norm_num
  · change (101 : ℝ)/237 ≤ 101/237 ∧ (61 : ℝ)/143 ≤ 61/143
    norm_num
  · change (89 : ℝ)/219 ≤ 89/219 ∧ (57 : ℝ)/137 ≤ 57/137
    norm_num

def finiteCylinderBase (cell : FinitePhaseCell) : ℕ :=
  cell.endpoint*3^(cell.m-cell.endpointDepth-cell.height)

def finiteCylinderSource (cell : FinitePhaseCell) (geometry : TailPhaseGeometry)
    (band : Fin 14) : LogSourceData :=
  { d := 0
    P := finiteCylinderBase cell*3^geometry.p+geometry.a
    Q := geometry.q
    p := (cell.m-cell.height)+geometry.p
    q := cell.verticalDepth+1
    band := finiteLogBand band }

theorem finiteCylinderBase_prefix (cell : FinitePhaseCell) (checked : cell.Checked) :
    ternaryPrefix (finiteCylinderBase cell) (cell.m-cell.height) = true := by
  have identity : cell.endpointDepth+(cell.m-cell.endpointDepth-cell.height) = cell.m-cell.height := by
    have depth := checked.1
    omega
  simpa only [finiteCylinderBase,Nat.add_zero,identity] using
    ternaryPrefix_append cell.endpoint 0 cell.endpointDepth (cell.m-cell.endpointDepth-cell.height)
      checked.2.2.1 (ternaryPrefix_zero _)

theorem finitePhaseCenter_identity (cell : FinitePhaseCell) (checked : cell.Checked) :
    finitePhaseCenter cell = 3^cell.height*finiteCylinderBase cell := by
  have power : (3 : ℕ)^(cell.m-cell.endpointDepth) =
      3^cell.height*3^(cell.m-cell.endpointDepth-cell.height) := by
    rw [← pow_add]
    congr 1
    have depth := checked.1
    omega
  unfold finitePhaseCenter finiteCylinderBase
  rw [power]
  ring

theorem finiteCylinderSource_identity (cell : FinitePhaseCell) (geometry : TailPhaseGeometry)
    (checked : cell.Checked) (depth : cell.height ≤ geometry.p) :
    finitePhaseCenter cell*finitePhaseLength cell geometry+geometry.a =
      finiteCylinderBase cell*3^geometry.p+geometry.a := by
  have power : (3 : ℕ)^cell.height*3^(geometry.p-cell.height) = 3^geometry.p := by
    rw [← pow_add]
    congr 1
    omega
  rw [finitePhaseCenter_identity cell checked]
  unfold finitePhaseLength
  calc
    (3^cell.height*finiteCylinderBase cell)*3^(geometry.p-cell.height)+geometry.a =
        finiteCylinderBase cell*(3^cell.height*3^(geometry.p-cell.height))+geometry.a := by ring
    _ = finiteCylinderBase cell*3^geometry.p+geometry.a := by rw [power]

theorem finiteCylinderSource_geometry (cell : FinitePhaseCell) (geometry : TailPhaseGeometry)
    (band : Fin 14) (n : ℕ) (exponent : 3 ≤ n) (cellChecked : cell.Checked)
    (checked : finitePhaseGeometryChecked cell geometry band)
    (coefficientLower : (cell.lower : ℝ) ≤ cell.denominator*((n : ℝ)/3^cell.m))
    (coefficientUpper : cell.denominator*((n : ℝ)/3^cell.m) ≤ (cell.upper : ℝ)) :
    (finiteCylinderSource cell geometry band).GeometryChecked n := by
  obtain ⟨depth,prefixA,boundA,prefixQ,lowerQ,boundQ,lower,upper⟩ := checked
  have basePositive : 0 < finiteCylinderBase cell := by
    unfold finiteCylinderBase
    have endpointPositive := cellChecked.2.1
    positivity
  have positiveP : 0 < finiteCylinderBase cell*3^geometry.p+geometry.a := by positivity
  have positiveQ : 0 < geometry.q := lt_of_lt_of_le (by positivity) lowerQ
  have prefixP := ternaryPrefix_append (finiteCylinderBase cell) geometry.a
    (cell.m-cell.height) geometry.p (finiteCylinderBase_prefix cell cellChecked) prefixA
  have boundP := ternaryPrefix_bound _ _ prefixP
  have identity := finiteCylinderSource_identity cell geometry cellChecked depth
  rw [identity] at lower upper
  have denominatorPositive : (0 : ℝ) < cell.denominator := by exact_mod_cast cellChecked.2.2.2.1
  rw [← mul_div_assoc] at coefficientLower coefficientUpper
  have scaledLower := (le_div_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ)^cell.m)).1 coefficientLower
  have scaledUpper := (div_le_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ)^cell.m)).1 coefficientUpper
  have lowerReal : ((finitePhaseBand band).1 : ℝ)*cell.denominator*
      ((finiteCylinderBase cell : ℝ)*3^geometry.p+geometry.a+1) <
      (finitePhaseBand band).2.1*cell.lower*geometry.q*(3 : ℝ)^cell.m := by exact_mod_cast lower
  have upperReal : ((finitePhaseBand band).2.2.2 : ℝ)*cell.upper*(geometry.q+1)*(3 : ℝ)^cell.m <
      (finitePhaseBand band).2.2.1*cell.denominator*
        ((finiteCylinderBase cell : ℝ)*3^geometry.p+geometry.a) := by exact_mod_cast upper
  have multipliedLower := mul_le_mul_of_nonneg_left scaledLower
    (show (0 : ℝ) ≤ (finitePhaseBand band).2.1*geometry.q by positivity)
  have multipliedUpper := mul_le_mul_of_nonneg_left scaledUpper
    (show (0 : ℝ) ≤ (finitePhaseBand band).2.2.2*(geometry.q+1) by positivity)
  have denominators : 0 < (finitePhaseBand band).2.1 ∧ 0 < (finitePhaseBand band).2.2.2 := by
    fin_cases band <;> decide
  have lowerRatio : ((finitePhaseBand band).1 : ℝ)/(finitePhaseBand band).2.1 <
      (n : ℝ)*geometry.q/((finiteCylinderBase cell : ℝ)*3^geometry.p+geometry.a+1) := by
    apply (div_lt_div_iff₀ (by exact_mod_cast denominators.1) (by positivity)).2
    apply (mul_lt_mul_iff_left₀ denominatorPositive).1
    nlinarith
  have upperRatio : (n : ℝ)*(geometry.q+1)/((finiteCylinderBase cell : ℝ)*3^geometry.p+geometry.a) <
      ((finitePhaseBand band).2.2.1 : ℝ)/(finitePhaseBand band).2.2.2 := by
    apply (div_lt_div_iff₀ (by positivity) (by exact_mod_cast denominators.2)).2
    apply (mul_lt_mul_iff_left₀ denominatorPositive).1
    nlinarith
  have inclusion := finiteLogBand_inclusion band
  apply LogSourceData.geometry_of_real_ratios n _ exponent positiveP positiveQ prefixP prefixQ boundP boundQ
  · simpa only [finiteCylinderSource,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      using inclusion.1.trans_lt lowerRatio
  · simpa only [finiteCylinderSource,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      using upperRatio.trans_le inclusion.2

end LambdaCantor.Integer

