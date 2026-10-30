# Trust boundary

The 45 final theorem/lemma axiom printouts have a union of:

- Lean standard axioms: `propext`, `Classical.choice`, `Quot.sound`.
- 15 registered external mathematical declarations (listed below).
- 1,753 generated native-computation axioms, explicitly authorized for finite checks.

In this Lean 4.32.1 installation, `native_decide` introduces per-evaluation
`_native.native_decide.ax...` declarations. This extends the trust boundary to
native evaluation and its compiler/runtime. These results are not claimed to
have only the three standard kernel axioms.

No final theorem depends on `sorryAx` or an unregistered explicit axiom.
The literal final Lean statements and assumptions are in THEOREMS.md and the
declaration map. The original audit checks source identity, statement mapping,
compilation evidence and printed axioms; it does not itself prove that prose
and formal statements have the same mathematical meaning.

## External mathematical declarations used by the final entry

| Declaration | Exact source | Registered sources and hypotheses |
| --- | --- | --- |
| `LambdaCantor.AE.ExternalPlancherel.complex_L1_of_fourier_L2` | [LambdaCantor/AE/ExternalPlancherelDensity.lean](Lean/LambdaCantor/AE/ExternalPlancherelDensity.lean#L48) | [EXTERNAL_THEOREMS-R025-LastAE.md](EXTERNAL_THEOREMS-R025-LastAE.md), [EXTERNAL_THEOREMS.md](EXTERNAL_THEOREMS.md) |
| `LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density` | [LambdaCantor/AE/ExternalPlancherelDensity.lean](Lean/LambdaCantor/AE/ExternalPlancherelDensity.lean#L40) | [EXTERNAL_THEOREMS-R025-LastAE.md](EXTERNAL_THEOREMS-R025-LastAE.md), [EXTERNAL_THEOREMS.md](EXTERNAL_THEOREMS.md) |
| `LambdaCantor.External.periodic_digits_of_coprime_denominator` | [LambdaCantor/External/Positional.lean](Lean/LambdaCantor/External/Positional.lean#L34) | [EXTERNAL_THEOREMS.md](EXTERNAL_THEOREMS.md) |
| `LambdaCantor.External.rational_of_eventually_periodic_digits` | [LambdaCantor/External/Positional.lean](Lean/LambdaCantor/External/Positional.lean#L26) | [EXTERNAL_THEOREMS.md](EXTERNAL_THEOREMS.md) |
| `LambdaCantor.External.wiles_fermat_last_theorem` | [LambdaCantor/Integer/ExternalFermat.lean](Lean/LambdaCantor/Integer/ExternalFermat.lean#L30) | [EXTERNAL_THEOREMS.md](EXTERNAL_THEOREMS.md) |
| `LambdaCantor.First.ExternalProjection.shmerkin2019_theorem62_four_maps` | [LambdaCantor/First/ExternalProjection.lean](Lean/LambdaCantor/First/ExternalProjection.lean#L52) | [EXTERNAL_THEOREMS-R025-First.md](EXTERNAL_THEOREMS-R025-First.md), [EXTERNAL_THEOREMS.md](EXTERNAL_THEOREMS.md) |
| `LambdaCantor.First.LinearRegularity.falconer2003_product73_interval` | [LambdaCantor/First/LinearRegularityProduct.lean](Lean/LambdaCantor/First/LinearRegularityProduct.lean#L25) | [EXTERNAL_THEOREMS-R025-First.md](EXTERNAL_THEOREMS-R025-First.md), [EXTERNAL_THEOREMS.md](EXTERNAL_THEOREMS.md) |
| `LambdaCantor.First.LinearRegularity.shmerkin2014_proposition23_two_maps` | [LambdaCantor/First/LinearRegularityExternal.lean](Lean/LambdaCantor/First/LinearRegularityExternal.lean#L79) | [EXTERNAL_THEOREMS-R025-First.md](EXTERNAL_THEOREMS-R025-First.md), [EXTERNAL_THEOREMS.md](EXTERNAL_THEOREMS.md) |
| `LambdaCantor.First.LinearRegularity.shmerkin2019_theorem92_uniform_l2` | [LambdaCantor/First/LinearRegularityExternal.lean](Lean/LambdaCantor/First/LinearRegularityExternal.lean#L56) | [EXTERNAL_THEOREMS-R025-First.md](EXTERNAL_THEOREMS-R025-First.md), [EXTERNAL_THEOREMS.md](EXTERNAL_THEOREMS.md) |
| `LambdaCantor.First.Roots.External.classical_compact_measure_l2_fourier_density` | [LambdaCantor/First/RootsExternalFourierDensity.lean](Lean/LambdaCantor/First/RootsExternalFourierDensity.lean#L24) | [EXTERNAL_THEOREMS-R025-First.md](EXTERNAL_THEOREMS-R025-First.md), [EXTERNAL_THEOREMS.md](EXTERNAL_THEOREMS.md) |
| `LambdaCantor.First.Roots.External.classical_plancherel_l1_l2` | [LambdaCantor/First/RootsExternalPlancherel.lean](Lean/LambdaCantor/First/RootsExternalPlancherel.lean#L27) | [EXTERNAL_THEOREMS-R025-First.md](EXTERNAL_THEOREMS-R025-First.md), [EXTERNAL_THEOREMS.md](EXTERNAL_THEOREMS.md) |
| `LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering` | [LambdaCantor/Last/ArithmeticDigitTheorem.lean](Lean/LambdaCantor/Last/ArithmeticDigitTheorem.lean#L40) | [EXTERNAL_SOURCE_CHECKS-R025-Root.md](EXTERNAL_SOURCE_CHECKS-R025-Root.md), [EXTERNAL_THEOREMS.md](EXTERNAL_THEOREMS.md) |
| `LambdaCantor.Last.External.mordell_smooth_plane_curve` | [LambdaCantor/Last/ArithmeticMordell.lean](Lean/LambdaCantor/Last/ArithmeticMordell.lean#L45) | [EXTERNAL_SOURCE_CHECKS-R025-Root.md](EXTERNAL_SOURCE_CHECKS-R025-Root.md), [EXTERNAL_THEOREMS.md](EXTERNAL_THEOREMS.md) |
| `LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation` | [LambdaCantor/Last/ExternalKronecker.lean](Lean/LambdaCantor/Last/ExternalKronecker.lean#L14) | [EXTERNAL_THEOREMS-R025-LastAE.md](EXTERNAL_THEOREMS-R025-LastAE.md), [EXTERNAL_THEOREMS.md](EXTERNAL_THEOREMS.md) |
| `LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma` | [LambdaCantor/Last/ExternalNewhouseBinary.lean](Lean/LambdaCantor/Last/ExternalNewhouseBinary.lean#L51) | [EXTERNAL_THEOREMS-R025-LastAE.md](EXTERNAL_THEOREMS-R025-LastAE.md), [EXTERNAL_THEOREMS.md](EXTERNAL_THEOREMS.md) |

The preserved registers include dated historical progress notes.
Their old “pending compilation” text is superseded by the accepted
2026-10-29 audit in `evidence/original-acceptance.json`.
Sixteen external names are registered; only the fifteen above occur
in the final entry's axiom union. Registration alone is not usage.
