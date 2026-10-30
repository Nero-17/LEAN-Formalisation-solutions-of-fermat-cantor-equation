import LambdaCantor.First.RootsFourierDensityInterface

/-!
# Established classical compact-measure Fourier converse

Primary source: Fernando Román García, arXiv:1801.09022v3,
Theorem 1.2(1), PDF page 2, https://arxiv.org/pdf/1801.09022 .
A compactly supported positive finite Radon measure on R^n whose Euclidean
Fourier transform belongs to L2 is g times Lebesgue measure for some g in L2.
Here n=1. Finite Borel measures on R are Radon. Positivity permits a globally
nonnegative measurable representative, and finiteness makes it L1.
The source uses (2*pi)^(-1/2) integral exp(-i*x*xi); mathlib charFun uses
integral exp(i*x*xi). Frequency reflection and multiplication by a nonzero
constant preserve membership in L2, so the hypothesis is equivalent.
This external statement is distinct from forward Plancherel and is not an
internal root-fibres or linear-regularity assertion.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots
namespace External

axiom classical_compact_measure_l2_fourier_density : ClassicalL2FourierDensityStatement

end External

/-- The only external step is the explicitly cited compact-measure converse;
the weighted-energy reduction and compact support are separate obligations. -/
theorem hasL2Density_of_weighted_energy (measure : Measure ℝ) [IsFiniteMeasure measure]
    (compact_support : ∃ support : Set ℝ, IsCompact support ∧ measure supportᶜ = 0)
    (order : ℝ) (order_nonnegative : 0 ≤ order)
    (finite_energy : (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ order *
      ‖charFun measure frequency‖ ^ 2)) ≠ ∞) : LinearRegularity.HasL2Density measure :=
  hasL2Density_of_weighted_energy_of_classical_converse
    External.classical_compact_measure_l2_fourier_density measure compact_support order order_nonnegative finite_energy

end LambdaCantor.First.Roots
