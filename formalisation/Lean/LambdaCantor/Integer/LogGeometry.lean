import LambdaCantor.Certificates.IntegerPackedLogDefinition

namespace LambdaCantor.Integer

theorem LogSourceData.geometry_of_real_ratios (n : ℕ) (source : LogSourceData)
    (exponent : 3 ≤ n) (positiveP : 0 < source.P) (positiveQ : 0 < source.Q)
    (prefixP : ternaryPrefix source.P source.p = true)
    (prefixQ : ternaryPrefix source.Q source.q = true)
    (boundP : source.P+1 ≤ 3^source.p) (boundQ : source.Q+1 ≤ 3^source.q)
    (lower : ((logSourceBand source.band).1 : ℝ)/(logSourceBand source.band).2.1 <
      (n : ℝ)*source.Q/(source.P+1))
    (upper : (n : ℝ)*(source.Q+1)/source.P <
      ((logSourceBand source.band).2.2.1 : ℝ)/(logSourceBand source.band).2.2.2) :
    source.GeometryChecked n := by
  have denominators : 0 < (logSourceBand source.band).2.1 ∧
      0 < (logSourceBand source.band).2.2.2 := by
    have allBands : ∀ band : Fin 10, 0 < (logSourceBand band).2.1 ∧
        0 < (logSourceBand band).2.2.2 := by decide
    exact allBands source.band
  refine ⟨exponent,positiveP,positiveQ,prefixP,prefixQ,boundP,boundQ,?_,?_⟩
  · have cleared := (div_lt_div_iff₀ (by exact_mod_cast denominators.1)
      (by positivity : (0 : ℝ) < source.P+1)).1 lower
    have ordered : ((logSourceBand source.band).1 : ℝ)*(source.P+1) <
        (logSourceBand source.band).2.1*n*source.Q := by nlinarith
    exact_mod_cast ordered
  · have cleared := (div_lt_div_iff₀ (by exact_mod_cast positiveP)
      (by exact_mod_cast denominators.2)).1 upper
    have ordered : ((logSourceBand source.band).2.2.2 : ℝ)*n*(source.Q+1) <
        (logSourceBand source.band).2.2.1*source.P := by nlinarith
    exact_mod_cast ordered

end LambdaCantor.Integer
