import LambdaCantor.Manuscript.First
import LambdaCantor.Manuscript.Classical
import LambdaCantor.Manuscript.SectionFour
import LambdaCantor.RealPowers.RealPowers
import LambdaCantor.Classical.GeneralCoverLocal
import LambdaCantor.Classical.PeriodicityConclusion
import LambdaCantor.Classical.GoodSlopeIsolation
import LambdaCantor.Classical.DimensionBounds
import LambdaCantor.PaperExamples.FirstSubdivision
import LambdaCantor.Integer.GoodSlopePositiveDimension
import LambdaCantor.Last.StrictReturnCriterion

/-! Full English-manuscript entry for commit
429d53bb243f49b19ba8169de0e82ed70050ec7f: all 34 numbered environments,
including the introduction, definitions and examples. This source is an
integration target, not a certificate of acceptance. Concrete low-partition
and large-layer production imports must exist and pass before this entry can
pass. MANUSCRIPT_DECLARATION_MAP.json records the exact declaration mapping.
The Classical and SectionFour wrappers can be compiled independently. -/
noncomputable section
namespace LambdaCantor.Manuscript

/-- Theorem 1.1, the introduction's all-real middle-third assertion. -/
theorem introductory_real_powers (exponent : ℝ) (above_one : 1 < exponent) :
    0 < dimH (intersection exponent (1/3)) :=
  RealPowers.real_powers_positive_dimension exponent above_one

end LambdaCantor.Manuscript

-- All 34 numbered environments, in manuscript order.
-- 1.1--1.4, introduction restatements.
#check LambdaCantor.Manuscript.introductory_real_powers
#check LambdaCantor.Manuscript.introductory_first_transition
#check LambdaCantor.Manuscript.introductory_last_transition
#check LambdaCantor.Manuscript.introductory_ae_dimension
-- 2.1 definition and its series/classical-Cantor bridge.
#check LambdaCantor.Manuscript.classicalCantor
#check LambdaCantor.Manuscript.classicalCircle
#check LambdaCantor.address_third_eq_ofDigits
#check LambdaCantor.cantorSet_third_eq
-- 2.2--2.11, including the full first-subdivision example.
#check LambdaCantor.Classical.rational_circle_axes
#check LambdaCantor.Manuscript.rational_classical_circle
#check LambdaCantor.Classical.general_cantor_image
#check LambdaCantor.Classical.coordinateBounds_of_partial_derivatives
#check LambdaCantor.Manuscript.classical_source_nonempty_compact
#check LambdaCantor.Classical.infDist_exclusive_domains_eventually_periodic
#check LambdaCantor.Classical.classical_circle_cardinality
#check LambdaCantor.PaperExamples.subdivisionResidual_identity
#check LambdaCantor.PaperExamples.first_subdivision_corner_table
#check LambdaCantor.Classical.source_first_digits_true
#check LambdaCantor.Classical.source_perfect
#check LambdaCantor.Last.strict_return_criterion
#check LambdaCantor.Classical.good_slope_infDist_eventually_periodic
#check LambdaCantor.Integer.good_slope_positive_dimension_of_perfect_subset
#check LambdaCantor.Classical.classical_circle_dimension_bounds
-- 3.1--3.10.
#check LambdaCantor.RealPowers.real_powers_positive_dimension_set
#check LambdaCantor.First.dimension_upper
#check LambdaCantor.First.first_lower
#check LambdaCantor.First.LinearRegularity.linear_regularity
#check LambdaCantor.First.Roots.root_fibres
#check LambdaCantor.First.irrational_parameters
#check LambdaCantor.First.irrational_onset
#check LambdaCantor.First.denominator
#check LambdaCantor.First.punctured_limit
#check LambdaCantor.First.powers_four
-- 4.1--4.9.
#check LambdaCantor.Last.two_band_separable_c1_closed_interval_criterion
#check LambdaCantor.Last.universal_lastTransition_lt_critical
#check LambdaCantor.Circle.circle_positive_measure
#check LambdaCantor.Circle.circle_onset
#check LambdaCantor.Circle.circle_zero_intervals
#check LambdaCantor.Circle.circle_known_separation
#check LambdaCantor.Manuscript.average_sobolev
#check LambdaCantor.AE.fullFourierEnergy_eq_convolution_energy
#check LambdaCantor.AE.fourier_density_eq_measureFourier
#check LambdaCantor.AE.irrational_ae_dimension_equality
#check LambdaCantor.Manuscript.ae_sqrt_two_dimension_bounds

-- BEGIN MANUSCRIPT DECLARATION AXIOM AUDIT
-- Generated from all 34 environments; actual acceptance remains pending.
#print axioms LambdaCantor.Manuscript.introductory_real_powers
#print axioms LambdaCantor.Manuscript.introductory_first_transition
#print axioms LambdaCantor.Manuscript.introductory_last_transition
#print axioms LambdaCantor.Manuscript.introductory_ae_dimension
#print axioms LambdaCantor.address_third_eq_ofDigits
#print axioms LambdaCantor.cantorSet_third_eq
#print axioms LambdaCantor.Manuscript.rational_classical_circle
#print axioms LambdaCantor.Classical.general_cantor_image
#print axioms LambdaCantor.Classical.coordinateBounds_of_partial_derivatives
#print axioms LambdaCantor.Manuscript.classical_source_nonempty_compact
#print axioms LambdaCantor.Classical.infDist_exclusive_domains_eventually_periodic
#print axioms LambdaCantor.Classical.classical_circle_cardinality
#print axioms LambdaCantor.PaperExamples.subdivisionResidual_identity
#print axioms LambdaCantor.PaperExamples.first_subdivision_corner_table
#print axioms LambdaCantor.Classical.source_first_digits_true
#print axioms LambdaCantor.Classical.source_perfect
#print axioms LambdaCantor.Classical.source_nonempty
#print axioms LambdaCantor.Classical.source_compact
#print axioms LambdaCantor.Last.strict_return_criterion
#print axioms LambdaCantor.Classical.good_slope_infDist_eventually_periodic
#print axioms LambdaCantor.Integer.good_slope_positive_dimension_of_perfect_subset
#print axioms LambdaCantor.Classical.classical_circle_dimension_bounds
#print axioms LambdaCantor.RealPowers.real_powers_positive_dimension_set
#print axioms LambdaCantor.First.dimension_upper
#print axioms LambdaCantor.First.first_lower
#print axioms LambdaCantor.First.LinearRegularity.linear_regularity
#print axioms LambdaCantor.First.Roots.root_fibres
#print axioms LambdaCantor.First.irrational_parameters
#print axioms LambdaCantor.First.irrational_onset
#print axioms LambdaCantor.First.denominator
#print axioms LambdaCantor.First.punctured_limit
#print axioms LambdaCantor.First.powers_four
#print axioms LambdaCantor.Last.two_band_separable_c1_closed_interval_criterion
#print axioms LambdaCantor.Last.universal_lastTransition_lt_critical
#print axioms LambdaCantor.Circle.circle_positive_measure
#print axioms LambdaCantor.Circle.circle_onset
#print axioms LambdaCantor.Circle.circle_zero_intervals
#print axioms LambdaCantor.Circle.circle_known_separation
#print axioms LambdaCantor.Manuscript.average_sobolev
#print axioms LambdaCantor.AE.fullFourierEnergy_eq_convolution_energy
#print axioms LambdaCantor.AE.fourier_density_eq_measureFourier
#print axioms LambdaCantor.AE.canonicalSobolevEnergy_eq_convolution_energy
#print axioms LambdaCantor.AE.canonicalSobolevEnergy_eq_densityFourier
#print axioms LambdaCantor.AE.irrational_ae_dimension_equality
#print axioms LambdaCantor.Manuscript.ae_sqrt_two_dimension_bounds
-- END MANUSCRIPT DECLARATION AXIOM AUDIT
