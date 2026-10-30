import LambdaCantor.Integer.TailPhaseGeometrySound
import LambdaCantor.Integer.PrefixConcatenation
import LambdaCantor.Certificates.IntegerPackedLogDefinition

namespace LambdaCantor.Integer

def tailLogBand (band : Fin 4) : Fin 10 :=
  match band.val with
  | 0 => ⟨0,by decide⟩
  | 1 => ⟨2,by decide⟩
  | 2 => ⟨5,by decide⟩
  | _ => ⟨7,by decide⟩

theorem tailLogBand_inclusion (band : Fin 4) :
    ((logSourceBand (tailLogBand band)).1 : ℝ)/(logSourceBand (tailLogBand band)).2.1 <
      ((tailPhaseBand band).1 : ℝ)/(tailPhaseBand band).2.1 ∧
    ((tailPhaseBand band).2.2.1 : ℝ)/(tailPhaseBand band).2.2.2 <
      ((logSourceBand (tailLogBand band)).2.2.1 : ℝ)/(logSourceBand (tailLogBand band)).2.2.2 := by
  fin_cases band
  · change (89 : ℝ)/73 < 11/9 ∧ (2027 : ℝ)/1624 < 171/137
    norm_num
  · change (89 : ℝ)/57 < 11/7 ∧ (21 : ℝ)/11 < 171/89
    norm_num
  · change (137 : ℝ)/171 < 1624/2027 ∧ (9 : ℝ)/11 < 73/89
    norm_num
  · change (89 : ℝ)/171 < 11/21 ∧ (7 : ℝ)/11 < 57/89
    norm_num

def tailCylinderSource (base baseDepth : ℕ) (geometry : TailPhaseGeometry) (band : Fin 4) : LogSourceData :=
  { d := 0
    P := base*3^geometry.p+geometry.a
    Q := geometry.q
    p := baseDepth+geometry.p
    q := 5
    band := tailLogBand band }

theorem tail_length_identity (geometry : TailPhaseGeometry) (depth : 3 ≤ geometry.p) :
    27*tailPhaseLength geometry = 3^geometry.p := by
  unfold tailPhaseLength
  rw [show (27 : ℕ) = 3^3 by decide,← pow_add]
  congr 1
  omega

theorem tailCylinderSource_geometry (n base baseDepth cell : ℕ) (geometry : TailPhaseGeometry)
    (band : Fin 4) (exponent : 3 ≤ n) (basePositive : 0 < base)
    (basePrefix : ternaryPrefix base baseDepth = true)
    (large : 1180980 ≤ 27*base) (checked : geometry.Checked cell band)
    (coefficientLower : 2*(cell : ℝ)-1 ≤ 4000*((n : ℝ)/(27*base)))
    (coefficientUpper : 4000*((n : ℝ)/(27*base)) ≤ 2*(cell : ℝ)+1) :
    (tailCylinderSource base baseDepth geometry band).GeometryChecked n := by
  have depth := checked.1
  have geometryPrefix := checked.2.2.1
  have verticalPrefix := checked.2.2.2.2.1
  have verticalPositive : 0 < geometry.q := by have bound := checked.2.2.2.2.2.1; omega
  have verticalBound := checked.2.2.2.2.2.2.1
  have horizontalPrefix := ternaryPrefix_append base geometry.a baseDepth geometry.p
    basePrefix geometryPrefix
  have horizontalPositive : 0 < base*3^geometry.p+geometry.a := by positivity
  have horizontalBound := ternaryPrefix_bound _ _ horizontalPrefix
  have inclusion := tailLogBand_inclusion band
  have ratios := checked.real_ratios geometry cell band (27*base) ((n : ℝ)/(27*base))
    (by exact_mod_cast large) coefficientLower coefficientUpper
  have denominatorIdentity : (27*(base : ℝ))*(tailPhaseLength geometry : ℝ)+geometry.a =
      (base : ℝ)*3^geometry.p+geometry.a := by
    have lengthIdentity : (27 : ℝ)*(tailPhaseLength geometry : ℝ) = (3 : ℝ)^geometry.p := by
      exact_mod_cast tail_length_identity geometry (by omega)
    calc
      (27*(base : ℝ))*tailPhaseLength geometry+geometry.a =
          (base : ℝ)*(27*tailPhaseLength geometry)+geometry.a := by ring
      _ = (base : ℝ)*3^geometry.p+geometry.a := by rw [lengthIdentity]
  have cancel : ((n : ℝ)/(27*base))*(27*base) = n := div_mul_cancel₀ _ (by positivity)
  have firstNumerator : ((n : ℝ)/(27*base))*geometry.q*(27*base) = n*geometry.q := by
    calc
      ((n : ℝ)/(27*base))*geometry.q*(27*base) =
          (((n : ℝ)/(27*base))*(27*base))*geometry.q := by ring
      _ = n*geometry.q := by rw [cancel]
  have secondNumerator : ((n : ℝ)/(27*base))*(geometry.q+1)*(27*base) = n*(geometry.q+1) := by
    calc
      ((n : ℝ)/(27*base))*(geometry.q+1)*(27*base) =
          (((n : ℝ)/(27*base))*(27*base))*(geometry.q+1) := by ring
      _ = n*(geometry.q+1) := by rw [cancel]
  rw [firstNumerator,secondNumerator,denominatorIdentity] at ratios
  have lower := inclusion.1.trans ratios.1
  have upper := ratios.2.trans inclusion.2
  have denominators : 0 < (logSourceBand (tailLogBand band)).2.1 ∧
      0 < (logSourceBand (tailLogBand band)).2.2.2 := by
    fin_cases band <;> decide
  refine ⟨exponent,horizontalPositive,verticalPositive,horizontalPrefix,verticalPrefix,
    horizontalBound,verticalBound,?_,?_⟩
  · have converted := (div_lt_div_iff₀ (by exact_mod_cast denominators.1)
      (by positivity : (0 : ℝ) < (base : ℝ)*3^geometry.p+geometry.a+1)).1 lower
    change (logSourceBand (tailLogBand band)).1*(base*3^geometry.p+geometry.a+1) <
      (logSourceBand (tailLogBand band)).2.1*n*geometry.q
    have ordered : ((logSourceBand (tailLogBand band)).1 : ℝ)*
        ((base : ℝ)*3^geometry.p+geometry.a+1) <
        (logSourceBand (tailLogBand band)).2.1*n*geometry.q := by nlinarith
    exact_mod_cast ordered
  · have converted := (div_lt_div_iff₀
      (by positivity : (0 : ℝ) < (base : ℝ)*3^geometry.p+geometry.a)
      (by exact_mod_cast denominators.2)).1 upper
    change (logSourceBand (tailLogBand band)).2.2.2*n*(geometry.q+1) <
      (logSourceBand (tailLogBand band)).2.2.1*(base*3^geometry.p+geometry.a)
    have ordered : ((logSourceBand (tailLogBand band)).2.2.2 : ℝ)*n*(geometry.q+1) <
        (logSourceBand (tailLogBand band)).2.2.1*((base : ℝ)*3^geometry.p+geometry.a) := by nlinarith
    exact_mod_cast ordered

end LambdaCantor.Integer
