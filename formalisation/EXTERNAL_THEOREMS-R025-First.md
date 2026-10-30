# First / Section 3 — current external-input register, R025

Updated 2026-10-24 18:43 UTC. Target manuscript commit: `429d53bb243f49b19ba8169de0e82ed70050ec7f`.

**R025 introduces no new external theorem or axiom in First.** The current First sources retain exactly the six inputs already registered during R018. In particular, no Rokhlin, Kallenberg, disintegration, conditional-probability, nonlinear root-law, conditional-dimension, or arithmetic endpoint axiom has been added. `RootsConditionalBase` and `RootsConditionalDensities` use Mathlib's `condDistrib` and measure APIs internally. Their static API review is not a compilation certificate; the full root-fibres theorem is still awaiting its actual check.

This current register makes the six retained declarations explicit for the coordinator's merge. It does not edit or replace the historical `EXTERNAL_THEOREMS.md`, and it is not a separate round archive. Authoritative exact Lean types and auxiliary definitions are in the cited source files.

## 1. Shmerkin 2019, Theorem 6.2

- Declaration: `LambdaCantor.First.ExternalProjection.shmerkin2019_theorem62_four_maps`.
- Source: `Lean/LambdaCantor/First/ExternalProjection.lean`.
- Quantifiers and hypotheses: every probability measure on the real line, contraction strictly between zero and one, and injective four-translation family; the measure must satisfy the actual equal-weight four-map affine fixed-point equation. There must be a positive separation constant such that at infinitely many depths all distinct words have translation separation at least that constant to the depth. For every positive exponent strictly below both one and `log 4 / log (1 / ratio)`, the conclusion gives a positive radius cutoff such that every ball of smaller positive radius has measure at most radius to that exponent.
- Primary source: Pablo Shmerkin, *On Furstenberg's intersection conjecture, self-similar measures, and the L^q norms of convolutions*, Annals of Mathematics 189 (2019), Theorem 6.2, printed page 368: [publisher PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v189-n2-p01-s.pdf).
- Specialization: four distinct equal-weight atoms have maximum weight one quarter. The all-radius constant, the actual projected Cantor law, invariance, separation, curve geometry, and the manuscript's intersection dimension upper bound are internal applications, not part of the axiom.

## 2. Shmerkin 2019, Theorem 9.2

- Declaration: `LambdaCantor.First.LinearRegularity.shmerkin2019_theorem92_uniform_l2`.
- Source: `Lean/LambdaCantor/First/LinearRegularityExternal.lean`.
- Quantifiers and hypotheses: every alphabet cardinality at least two, open preconnected domain in the real parameter plane, analytic contraction and analytic translations on a neighborhood of the domain, with contraction strictly between zero and one. For every pair of distinct infinite addresses, their actual infinite translation sums must differ at some parameter in the domain.
- Conclusion: there exists an exceptional subset of the domain with Hausdorff dimension at most one. At every parameter outside it, if the translations are injective and the contraction exceeds the reciprocal alphabet cardinality, every probability measure satisfying the actual equal-weight self-similar fixed-point equation has a globally nonnegative measurable real density which is in both L1 and L2 and represents the measure by `volume.withDensity`.
- Primary source: the same [publisher PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v189-n2-p01-s.pdf), Theorem 9.2, printed page 385; [author version](https://arxiv.org/html/1609.07802v3#S9.Thmtheorem9.2).
- Application: the actual analytic finite-block family, connected parameter rectangles, infinite-address nondegeneracy, distinctness, contraction inequality, probability law and invariant-law equation are proved in the linear branch. The axiom does not assert `linear_regularity` or any root-fibre conclusion.

## 3. Shmerkin 2014, Proposition 2.3

- Declaration: `LambdaCantor.First.LinearRegularity.shmerkin2014_proposition23_two_maps`.
- Source: `Lean/LambdaCantor/First/LinearRegularityExternal.lean`.
- Quantifiers and conclusion: there exists a Hausdorff-dimension-zero exceptional contraction set contained in the open unit interval, independent of the translations. For every contraction outside it, every injective two-translation family and every probability measure satisfying its actual fair two-map fixed-point equation, there are positive decay exponent and constant such that the norm of its characteristic function is bounded by the constant times frequency magnitude to the negative exponent at all frequency magnitudes at least one.
- Primary source: Pablo Shmerkin (2014), Proposition 2.3, [author version](https://arxiv.org/html/1303.3992v2#S2.SS2.Thmproposition2.3).
- Application: sparse block factors, all positive contraction-power preimages, actual fair sparse law, Fourier-frequency normalization and convolution with the dense factor are internal. The exceptional set is uniform over all distinct real translations, exactly as retained in the declaration.

## 4. Falconer 2003, Product formula 7.3

- Declaration: `LambdaCantor.First.LinearRegularity.falconer2003_product73_interval`.
- Source: `Lean/LambdaCantor/First/LinearRegularityProduct.lean`.
- Exact specialization: for every real set and every ordered pair of real interval endpoints, Hausdorff dimension of the set times that closed interval is at most Hausdorff dimension of the set plus one. No measurability or boundedness of the first factor is assumed.
- Primary source: Kenneth Falconer, *Fractal Geometry*, second edition (2003), Product formula 7.3, equation (7.7), printed page 102: [publisher chapter](https://doi.org/10.1002/0470013850.ch7). The retained source ledger checked the primary book text, PDF page 128, through [this book copy](https://www.muslimuniversity.edu.af/uploads/library/Fractal.Geometry.Mathematical.Foundations.and.Applications.Second.Edition.eBook-EEn_957.pdf).
- Application: the second factor has upper box dimension at most one. Passing from bounded slope intervals to the whole real line and from the contraction exception to all block-power exceptions is internal. Lean's max product metric and the Euclidean metric are bi-Lipschitz equivalent.

## 5. Classical forward Plancherel for the actual L1 Fourier integral

- Declaration: `LambdaCantor.First.Roots.External.classical_plancherel_l1_l2`.
- Source: `Lean/LambdaCantor/First/RootsExternalPlancherel.lean`.
- Exact specialization: every complex-valued real-line function which is integrable and belongs to L2 has its actual integral Fourier transform in L2, and the integral of the squared norm of that transform equals the integral of the squared norm of the function. The transform is Mathlib's `VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)`, with kernel `exp(-2*pi*i*x*frequency)`.
- Primary source: Terence Tao, *247B, Notes 1: Restriction theory*, 29 March 2020, introductory equations (1) and (3): [author notes](https://terrytao.wordpress.com/2020/03/29/247b-notes-1-restriction-theory/).
- Application: actual dense L2 density energy, sparse/dense Sobolev convolution, Fourier density differences, interpolation and kernel density estimates. All hypotheses concern an already existing L1/L2 density; this input alone does not give density existence from characteristic-function energy.

## 6. Classical compact-measure L2 Fourier converse

- Declaration: `LambdaCantor.First.Roots.External.classical_compact_measure_l2_fourier_density`.
- Sources: `Lean/LambdaCantor/First/RootsExternalFourierDensity.lean` and the exact proposition `ClassicalL2FourierDensityStatement` in `RootsFourierDensityInterface.lean`.
- Exact retained type: every finite positive Borel measure on the real line which gives full measure to some compact set and whose actual characteristic function belongs to L2 has a globally nonnegative measurable real density, integrable and in L2, representing the actual measure by `volume.withDensity (ENNReal.ofReal density)`.
- Primary source: Fernando Román García, *A Fourier Coefficients Approach to Hausdorff Dimension in the Heisenberg Group*, arXiv:1801.09022v3, Theorem 1.2(1), PDF page 2: [primary PDF](https://arxiv.org/pdf/1801.09022), [HTML](https://arxiv.org/html/1801.09022). This is the Euclidean theorem in the introduction, specialized to dimension one. Finite Borel measures on the real line are Radon; positivity and finiteness permit the retained nonnegative L1 representative.
- Normalization: the source uses `(2*pi)^(-1/2) * integral exp(-i*x*frequency)`, while Mathlib `charFun` uses the positive sign without that constant. Frequency reflection and multiplication by a nonzero constant preserve L2 membership. No quantitative norm identity is added to the converse.
- Application: density existence at every compact good-energy representative, including possible parameters in a Shmerkin exceptional set. Actual compact support and weighted-energy-to-characteristic-L2 are internal obligations. This axiom contains no Cantor set, exponent parameter, selected root, root law, conditional law or Hausdorff-dimension conclusion.
- Bibliographic correction preserved: the paper's reference [22] is Mattila, *Geometry of Sets and Measures in Euclidean Spaces* (1995), page 31, not *Fourier Analysis and Hausdorff Dimension*. The directly checked primary statement is Román García's theorem; no independent check of that cited book page is claimed.

## Actual audit distinction

The successful current-source `Section3DimensionAudit` prints:

- `dimension_upper` and `first_lower`: standard Lean axioms plus input 1.
- Both actual linear regularity endpoints: standard Lean axioms plus inputs 2–5.
- Actual state-continuity/nullity and both conditional dimension transfer endpoints: only `propext`, `Classical.choice`, `Quot.sound`.

The actual `RootsAbsoluteContinuityAudit` subsequently passed on 2026-10-27 at 03:10:41.5566095 UTC, SHA256 `1632B10C9D9A8DDA663CCCB90F81EB459CBFBA564E2ED179AF24C95FC6155DB2`, EXIT=0. The actual L1 convergence, compact-good-set density and compact-good-set AC endpoints print only the standard three Lean axioms plus inputs 5 and 6. The full actual `rootFibreData_rootLaw_absolutelyContinuous` prints the standard three plus inputs 2–6. It does not depend on input 1. Actual AC module SHA256 is `9366C9C89260884A7D9A9A120B6E3FC36EC1690BDD40A396B121231AACA2DB7A`, EXIT=0 at 03:09:22.0433604 UTC. All compact density, weak identification, state-nullity and exhaustion premises are internally discharged from `RootFibreData`.

The full actual `root_fibres` (AC and root-law-almost-everywhere exact actual intersection dimension, with only geometric `RootFibreData`) subsequently passed: `RootsMain.lean` SHA256 `09FCC6C7129D33256B1FF156173D970880544C6E989CEA28F71D00439FA5CC14`, EXIT=0 at 2026-10-27 03:59:07.9940293 UTC. Its actual `RootsTrustAudit` SHA256 `34E2F7DCC0ECEEC3560D5DFB57BC52318F314D9045518C22642276E662059B19` passed EXIT=0 at 04:01:31.3191091 UTC. Exact printed dependencies are standard three plus inputs 1–6. The local good-set exact-dimension endpoint uses standard three plus inputs 1, 5 and 6. The local prefix L1 limit and actual positive-density range endpoints use standard three plus inputs 5 and 6. This is an actual current-source trust audit; all internal regularity, density, conditional probability, replacement, tail summability and exhaustion premises have been discharged.

The final arithmetic audit also passed. `RationalEndpoints.lean` SHA256 `C11662AA931AE915A11352B08F9406885D53E0E5C3DCD2213C3E7BD9C6CA387C` passed EXIT=0 at 2026-10-27 04:06:02.3013392 UTC. `Section3TerminalAudit.lean` SHA256 `A77881D17D1EBB78B6F5A159275F1340CE0582FC40458F1029BD48FCC0F1FE57` passed EXIT=0 at 04:07:26.4444869 UTC, printing actual types and actual dependencies of irrational_parameters, irrational_onset, denominator, denominator_rat, punctured_limit, continuity_iff_quarter and powers_four. Each uses exactly the standard three Lean axioms plus inputs 1–6. No caller root-law, density, regularity, conditional-measure, prefix or root-family premise remains in these public endpoints.

Current-source acceptance was subsequently checked by `Lean/LambdaCantor/First/section3_acceptance.py`: all 24 required audited endpoint entries accepted, no missing endpoint, and no inherited missing-log baseline. All 197 modules in the current First queue (excluding the unused legacy CircleRootFibreAdapter, not imported by these targets) have strict current-source EXIT=0 certificates. Frozen manuscript main.tex SHA256 remains `FB69B3D7DF3E2FC5ED3AFD2EAD28E3C4C2B613CEC237CEA224342E38A7D8565F` for commit 429d53bb243f49b19ba8169de0e82ed70050ec7f. Section 3.1 is coordinated separately and is not claimed by First.

The requested First theorem chain and its trust audit are complete. No `sorry`/`admit` implementation, native axiom or manuscript-target axiom has been introduced; R025 new external inputs remain zero. The six retained classical inputs above remain explicit external assumptions; they have not been presented as proved internally in this project.
