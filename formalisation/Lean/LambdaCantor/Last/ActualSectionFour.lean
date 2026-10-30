import LambdaCantor.Last.SectionFourLastAE
import LambdaCantor.Circle.ManuscriptEndpoints
import LambdaCantor.Circle.ZeroIntervalsTrustAudit

/-! The seven main Section 4 endpoint audit for frozen manuscript
429d53bb243f49b19ba8169de0e82ed70050ec7f. The Circle and First dependencies
remain owned by the coordinating queues. This file is a build target, not a
certificate until its actual compilation and complete axiom output pass.
The literal averaged-Sobolev lemma and sqrt(2) example also require their
separate manuscript wrappers; these seven prints alone do not certify all
Section 4 statements. -/

#print axioms LambdaCantor.Last.two_band_separable_c1_closed_interval_criterion
#print axioms LambdaCantor.Last.universal_lastTransition_lt_critical
#print axioms LambdaCantor.Circle.circle_positive_measure
#print axioms LambdaCantor.Circle.circle_onset
#print axioms LambdaCantor.Circle.circle_zero_intervals
#print axioms LambdaCantor.Circle.circle_known_separation
#print axioms LambdaCantor.AE.irrational_ae_dimension_equality
