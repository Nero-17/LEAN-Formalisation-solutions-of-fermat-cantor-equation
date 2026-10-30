import LambdaCantor.Common
import Mathlib.Analysis.Analytic.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Established external inputs for the linear regularity construction

The two axioms below are explicit specializations of published theorems.
They do not assert the manuscript's linear-regularity or root-fibres lemma.

* Shmerkin, Annals of Mathematics 189 (2019), Theorem 9.2, p.385:
  https://arxiv.org/html/1609.07802v3#S9.Thmtheorem9.2
  https://annals.math.princeton.edu/wp-content/uploads/annals-v189-n2-p01-s.pdf
  Specialization: two real parameters, positive contraction, q=2, equal
  weights, and distinct translations at the parameter of application.
  The atomic q-mass is then 1/alphabetSize. Connectedness is included in
  the open-domain hypotheses. Nondegeneracy is imposed on actual infinite
  address sums, not replaced by a formal family label.

* Shmerkin, Geometric and Functional Analysis 24 (2014), Proposition 2.3:
  https://arxiv.org/html/1303.3992v2#S2.SS2.Thmproposition2.3
  Specialization: two distinct translations with equal positive weights.
  The zero-dimensional exceptional set is independent of the translations.
  Fourier decay is stated in the equivalent charFun convention exp(i*x*xi).
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace LambdaCantor.First.LinearRegularity

/-- The actual equal-weight affine fixed-point equation. -/
def IsUniformSelfSimilar (alphabetSize : ℕ) (measure : Measure ℝ)
    (contraction : ℝ) (translation : Fin alphabetSize → ℝ) : Prop :=
  measure = ∑ symbol : Fin alphabetSize, (alphabetSize : ℝ≥0∞)⁻¹ •
    Measure.map (fun point : ℝ => contraction * point + translation symbol) measure

/-- A nonnegative real L2 density representing the actual measure. -/
def HasL2Density (measure : Measure ℝ) : Prop :=
  ∃ density : ℝ → ℝ, (∀ point, 0 ≤ density point) ∧ Measurable density ∧
    Integrable density volume ∧ MemLp density 2 volume ∧
      measure = volume.withDensity (fun point => ENNReal.ofReal (density point))

/-- Power Fourier decay at large frequencies, with constants depending on
this measure, as in the published theorem. -/
def HasPowerFourierDecay (measure : Measure ℝ) : Prop :=
  ∃ exponent constant : ℝ, 0 < exponent ∧ 0 < constant ∧
    ∀ frequency : ℝ, 1 ≤ |frequency| →
      ‖charFun measure frequency‖ ≤ constant * |frequency| ^ (-exponent)

/-- Established external theorem, Shmerkin 2019 Theorem 9.2, q=2 and two
parameters. The distinct-translation condition ensures that the finite
atomic 2-mass is exactly the reciprocal of the alphabet cardinality. -/
axiom shmerkin2019_theorem92_uniform_l2
    (alphabetSize : ℕ) (halphabet : 2 ≤ alphabetSize)
    (domain : Set (ℝ × ℝ)) (hopen : IsOpen domain) (hconnected : IsPreconnected domain)
    (contraction : (ℝ × ℝ) → ℝ)
    (translation : (ℝ × ℝ) → Fin alphabetSize → ℝ)
    (hcontractionAnalytic : AnalyticOnNhd ℝ contraction domain)
    (htranslationAnalytic : ∀ symbol, AnalyticOnNhd ℝ (fun parameter => translation parameter symbol) domain)
    (hcontraction : ∀ parameter ∈ domain, 0 < contraction parameter ∧ contraction parameter < 1)
    (hnondegenerate : ∀ left right : ℕ → Fin alphabetSize, left ≠ right →
      ∃ parameter ∈ domain,
        (∑' index, translation parameter (left index) * contraction parameter ^ index) ≠
        ∑' index, translation parameter (right index) * contraction parameter ^ index) :
    ∃ exceptional : Set (ℝ × ℝ), exceptional ⊆ domain ∧ dimH exceptional ≤ 1 ∧
      ∀ parameter ∈ domain, parameter ∉ exceptional →
        Function.Injective (translation parameter) →
        (alphabetSize : ℝ)⁻¹ < contraction parameter →
        ∀ measure : Measure ℝ, IsProbabilityMeasure measure →
          IsUniformSelfSimilar alphabetSize measure (contraction parameter) (translation parameter) →
          HasL2Density measure

/-- Established external theorem, Shmerkin 2014 Proposition 2.3, specialized
to fair two-map systems. The exceptional contraction set is uniform over
all choices of distinct real translations. -/
axiom shmerkin2014_proposition23_two_maps :
    ∃ exceptional : Set ℝ, exceptional ⊆ Set.Ioo (0 : ℝ) 1 ∧ dimH exceptional = 0 ∧
      ∀ contraction ∈ Set.Ioo (0 : ℝ) 1, contraction ∉ exceptional →
        ∀ translation : Fin 2 → ℝ, Function.Injective translation →
          ∀ measure : Measure ℝ, IsProbabilityMeasure measure →
            IsUniformSelfSimilar 2 measure contraction translation → HasPowerFourierDecay measure

end LambdaCantor.First.LinearRegularity

