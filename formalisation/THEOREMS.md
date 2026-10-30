# Frozen manuscript to Lean declarations

Scope: Overleaf commit `429d53bb243f49b19ba8169de0e82ed70050ec7f`.

All 34 numbered English environments, including introductory restatements,
definitions and examples, are included. This table is generated from the
accepted declaration map; the JSON map contains the exact TeX and Lean statements.

| Number | Kind | Lean declarations |
| --- | --- | --- |
| 1.1 | theorem | [`LambdaCantor.Manuscript.introductory_real_powers`](Lean/LambdaCantor/Manuscript/All.lean) |
| 1.2 | theorem | [`LambdaCantor.Manuscript.introductory_first_transition`](Lean/LambdaCantor/Manuscript/First.lean) |
| 1.3 | theorem | [`LambdaCantor.Manuscript.introductory_last_transition`](Lean/LambdaCantor/Manuscript/SectionFour.lean) |
| 1.4 | theorem | [`LambdaCantor.Manuscript.introductory_ae_dimension`](Lean/LambdaCantor/Manuscript/SectionFour.lean) |
| 2.1 | definition | [`LambdaCantor.Manuscript.classicalCantor`](Lean/LambdaCantor/Manuscript/Classical.lean)<br>[`LambdaCantor.Manuscript.classicalCircle`](Lean/LambdaCantor/Manuscript/Classical.lean)<br>[`LambdaCantor.address`](Lean/LambdaCantor/Common.lean)<br>[`LambdaCantor.address_third_eq_ofDigits`](Lean/LambdaCantor/ClassicalBridge.lean)<br>[`LambdaCantor.cantorSet_third_eq`](Lean/LambdaCantor/ClassicalBridge.lean) |
| 2.2 | lemma | [`LambdaCantor.Manuscript.rational_classical_circle`](Lean/LambdaCantor/Manuscript/Classical.lean) |
| 2.3 | lemma | [`LambdaCantor.Classical.general_cantor_image`](Lean/LambdaCantor/Classical/GeneralCoverLocal.lean)<br>[`LambdaCantor.Classical.coordinateBounds_of_partial_derivatives`](Lean/LambdaCantor/Classical/GeneralCover.lean) |
| 2.4 | proposition | [`LambdaCantor.Manuscript.classical_source_nonempty_compact`](Lean/LambdaCantor/Manuscript/Classical.lean)<br>[`LambdaCantor.Classical.source`](Lean/LambdaCantor/Classical/Source.lean) |
| 2.5 | lemma | [`LambdaCantor.Classical.infDist_exclusive_domains_eventually_periodic`](Lean/LambdaCantor/Classical/PeriodicityConclusion.lean) |
| 2.6 | theorem | [`LambdaCantor.Classical.classical_circle_cardinality`](Lean/LambdaCantor/Classical/NoIsolation.lean) |
| 2.7 | example | [`LambdaCantor.PaperExamples.subdivisionResidual_identity`](Lean/LambdaCantor/PaperExamples/FirstSubdivision.lean)<br>[`LambdaCantor.PaperExamples.first_subdivision_corner_table`](Lean/LambdaCantor/PaperExamples/FirstSubdivision.lean)<br>[`LambdaCantor.Classical.source_first_digits_true`](Lean/LambdaCantor/Classical/FirstSubdivision.lean)<br>[`LambdaCantor.Classical.source_perfect`](Lean/LambdaCantor/Classical/NoIsolation.lean)<br>[`LambdaCantor.Classical.source_nonempty`](Lean/LambdaCantor/Classical/Source.lean)<br>[`LambdaCantor.Classical.source_compact`](Lean/LambdaCantor/Classical/Source.lean)<br>[`LambdaCantor.Classical.general_cantor_image`](Lean/LambdaCantor/Classical/GeneralCoverLocal.lean) |
| 2.8 | lemma | [`LambdaCantor.Last.strict_return_criterion`](Lean/LambdaCantor/Last/StrictReturnCriterion.lean) |
| 2.9 | lemma | [`LambdaCantor.Classical.good_slope_infDist_eventually_periodic`](Lean/LambdaCantor/Classical/GoodSlopeIsolation.lean)<br>[`LambdaCantor.Integer.GoodSlope`](Lean/LambdaCantor/Integer/GoodSlopes.lean) |
| 2.10 | lemma | [`LambdaCantor.Integer.good_slope_positive_dimension_of_perfect_subset`](Lean/LambdaCantor/Integer/GoodSlopePositiveDimension.lean) |
| 2.11 | theorem | [`LambdaCantor.Classical.classical_circle_dimension_bounds`](Lean/LambdaCantor/Classical/DimensionBounds.lean) |
| 3.1 | theorem | [`LambdaCantor.RealPowers.real_powers_positive_dimension_set`](Lean/LambdaCantor/RealPowers/RealPowers.lean) |
| 3.2 | theorem | [`LambdaCantor.First.dimension_upper`](Lean/LambdaCantor/First/Upper.lean)<br>[`LambdaCantor.First.dimensionUpperBound`](Lean/LambdaCantor/First/Dimension.lean) |
| 3.3 | corollary | [`LambdaCantor.First.first_lower`](Lean/LambdaCantor/First/Upper.lean) |
| 3.4 | lemma | [`LambdaCantor.First.LinearRegularity.linear_regularity`](Lean/LambdaCantor/First/LinearRegularityMain.lean)<br>[`LambdaCantor.First.LinearRegularity.HasPositiveSobolevDensity`](Lean/LambdaCantor/First/LinearRegularityRectangle.lean) |
| 3.5 | lemma | [`LambdaCantor.First.Roots.root_fibres`](Lean/LambdaCantor/First/RootsMain.lean)<br>[`LambdaCantor.First.Roots.RootFibreData`](Lean/LambdaCantor/First/RootFibreInterface.lean)<br>[`LambdaCantor.First.Roots.RootFibreConclusion`](Lean/LambdaCantor/First/RootFibreInterface.lean) |
| 3.6 | theorem | [`LambdaCantor.First.irrational_parameters`](Lean/LambdaCantor/First/RationalEndpoints.lean) |
| 3.7 | theorem | [`LambdaCantor.First.irrational_onset`](Lean/LambdaCantor/First/RationalEndpoints.lean) |
| 3.8 | theorem | [`LambdaCantor.First.denominator`](Lean/LambdaCantor/First/RationalEndpoints.lean) |
| 3.9 | theorem | [`LambdaCantor.First.punctured_limit`](Lean/LambdaCantor/First/RationalEndpoints.lean) |
| 3.10 | proposition | [`LambdaCantor.First.powers_four`](Lean/LambdaCantor/First/RationalEndpoints.lean) |
| 4.1 | lemma | [`LambdaCantor.Last.two_band_separable_c1_closed_interval_criterion`](Lean/LambdaCantor/Last/TwoBandSeparableClosed.lean) |
| 4.2 | theorem | [`LambdaCantor.Last.universal_lastTransition_lt_critical`](Lean/LambdaCantor/Last/UniversalLastConclusion.lean) |
| 4.3 | theorem | [`LambdaCantor.Circle.circle_positive_measure`](Lean/LambdaCantor/Circle/ManuscriptEndpoints.lean)<br>[`LambdaCantor.Circle.onset`](Lean/LambdaCantor/Circle/OnsetAlgebra.lean) |
| 4.4 | theorem | [`LambdaCantor.Circle.circle_onset`](Lean/LambdaCantor/Circle/ManuscriptEndpoints.lean)<br>[`LambdaCantor.Circle.onset`](Lean/LambdaCantor/Circle/OnsetAlgebra.lean) |
| 4.5 | theorem | [`LambdaCantor.Circle.circle_zero_intervals`](Lean/LambdaCantor/Circle/ZeroIntervalSequence.lean)<br>[`LambdaCantor.Circle.onset`](Lean/LambdaCantor/Circle/OnsetAlgebra.lean) |
| 4.6 | theorem | [`LambdaCantor.Circle.circle_known_separation`](Lean/LambdaCantor/Circle/ManuscriptEndpoints.lean)<br>[`LambdaCantor.Circle.onset`](Lean/LambdaCantor/Circle/OnsetAlgebra.lean) |
| 4.7 | lemma | [`LambdaCantor.Manuscript.average_sobolev`](Lean/LambdaCantor/Manuscript/AverageSobolev.lean)<br>[`LambdaCantor.AE.fullFourierEnergy_eq_convolution_energy`](Lean/LambdaCantor/AE/ConvolutionMeasure.lean)<br>[`LambdaCantor.AE.fourier_density_eq_measureFourier`](Lean/LambdaCantor/AE/SobolevDensity.lean)<br>[`LambdaCantor.AE.HasSobolevDensity`](Lean/LambdaCantor/AE/SobolevDensity.lean)<br>[`LambdaCantor.AE.selfConvolutionProbability`](Lean/LambdaCantor/AE/ConvolutionMeasureCore.lean)<br>[`LambdaCantor.AE.canonicalSobolevEnergy`](Lean/LambdaCantor/AE/CanonicalSobolevEnergy.lean)<br>[`LambdaCantor.AE.HasCanonicalSobolevDensity`](Lean/LambdaCantor/AE/CanonicalSobolevEnergy.lean)<br>[`LambdaCantor.AE.canonicalSobolevEnergy_eq_convolution_energy`](Lean/LambdaCantor/AE/CanonicalSobolevEnergy.lean)<br>[`LambdaCantor.AE.canonicalSobolevEnergy_eq_densityFourier`](Lean/LambdaCantor/AE/CanonicalSobolevEnergy.lean) |
| 4.8 | theorem | [`LambdaCantor.AE.irrational_ae_dimension_equality`](Lean/LambdaCantor/AE/ActualDimensionTerminal.lean) |
| 4.9 | example | [`LambdaCantor.Manuscript.ae_sqrt_two_dimension_bounds`](Lean/LambdaCantor/Manuscript/SectionFour.lean) |
