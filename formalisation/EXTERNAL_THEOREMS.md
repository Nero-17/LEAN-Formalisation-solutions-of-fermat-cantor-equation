# External theorem registry

The user authorizes well-known external results as black boxes. Each declaration below is an explicit trusted axiom, not a Lean proof. Article-specific conclusions may not be hidden here. Final results must list their transitive external dependencies via `#print axioms`.

## Classical positional-expansion theorem

Module: `Lean/LambdaCantor/External/Positional.lean`.

Declarations: `rational_of_eventually_periodic_digits`; `periodic_digits_of_coprime_denominator`.

Source: Adamczewski, Frougny, Siegel, Steiner, *Rational numbers with purely periodic beta-expansion*, Introduction p.1, explicitly recalling the integer-base theorem and referring to Hardy–Wright: https://www.irif.fr/~steiner/AFSS.pdf . Also eventual periodicity is given in Florian Breuer's lecture notes *Some Base Results*, Theorem8.0.3: https://carmamaths.org/florianbreuer/MATH3170/Chap-Some_Base_Results.html .

Assumptions: integer base≥2, actual positional digits; for pure periodicity the rational is in (0,1) and its reduced denominator is coprime to the base. The terminating/repeating-maximal ambiguity is harmless for eventual periodicity and excluded by these interior/coprimality conditions in the pure case.

These inputs replace only standard number-system theory. Rational-point exclusion on the circle, digit graph constraints, and the isolation argument remain internal proof obligations.

## Fermat's Last Theorem

Module: `Lean/LambdaCantor/Integer/ExternalFermat.lean` (pending compilation).

Declaration: `LambdaCantor.External.wiles_fermat_last_theorem : FermatLastTheorem`.

Exact imported mathlib proposition: for natural exponent at least3 and nonzero natural coordinates, the Fermat equation has no solution. Clearing rational denominators is proved by the existing mathlib equivalence and the internal `Integer/Fermat.lean` bridge; it is not another external assumption.

Primary sources verified by the integer implementation agent: Wiles, *Modular elliptic curves and Fermat's Last Theorem*, Annals141 (1995),443–551, https://annals.math.princeton.edu/1995/141-3/p01 ; Taylor–Wiles, *Ring-theoretic properties of certain Hecke algebras*, Annals141 (1995),553–572, https://annals.math.princeton.edu/1995/141-3/p02 .

Application requires exponent≥3 and nonzero rational physical coordinates. Cantor source existence, perfectness, all slope certificates and dimension bounds remain internal obligations.

## Authorized native computation (Lean 4.32.1)
User explicitly accepted native_decide for finite certificates. Inspection of installed src/lean/Lean/Meta/Native.lean confirms nativeEqTrue compiles and evaluates a closed Boolean, then introduces a per-evaluation _native.native_decide.ax axiom. This supersedes the preliminary Lean.ofReduceBool description. Final #print axioms output must list the actual generated declarations; this is a computational trust extension, not a black-box assumption of the article theorem.

## Finite-alphabet probability extension

Module: `Lean/LambdaCantor/Circle/ExternalCylinderExtension.lean` (pending compilation).

Declaration: `LambdaCantor.Circle.External.finite_alphabet_cylinder_extension`.

This is the finite discrete specialization of the Kolmogorov extension theorem: nonnegative prefix masses, normalized at the empty word and consistent under summation over the next letter, extend to a probability measure with exactly those cylinder masses. The alphabet is finite and nonempty, with measurable singletons. The source declaration cites Kallenberg, *Foundations of Modern Probability*, third edition (2021), Theorem 8.24 (Ionescu–Tulcea); the corresponding general construction also exists in `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean`.

Only the standard measure-extension step is external. Prefix consistency, quantitative mass bounds, geometric coding, support on the circle, and the Hausdorff dimension conclusion remain internal obligations. This declaration is not yet a checked dependency of a completed positive-dimension theorem.


## First / Section 2 — established external inputs (R018, verified source ledger 2026-10-21)

The following five declarations are standard published inputs. None asserts this manuscript's dimension-upper, linear-regularity, nonlinear root-fibres, or onset conclusion. Each paper-specific construction, probability-law identification, separation/nondegeneracy check, coupling, and dimension deduction remains an internal proof obligation. Compilation status below is as of09:40UTC and does not replace final terminal `#print axioms` on completed target theorems.

### Shmerkin2019, Theorem6.2: small-ball bound from exponential separation

Module: `Lean/LambdaCantor/First/ExternalProjection.lean` (EXIT0).
Declaration: `LambdaCantor.First.ExternalProjection.shmerkin2019_theorem62_four_maps`.
Primary source: Shmerkin, Annals of Mathematics189 (2019), Theorem6.2, printedp368, https://annals.math.princeton.edu/wp-content/uploads/annals-v189-n2-p01-s.pdf ; author version https://arxiv.org/html/1609.07802v3 .
Exact specialization: real homogeneous four-map IFS with common positive contraction below1, four distinct translations, equal weights, actual invariant probability law, and explicit finite-word exponential separation. For every positive exponent strictly below min(log4/log(1/lambda),1), all sufficiently small balls have mass at most radius to that exponent. The all-radius multiplicative-constant extension is proved internally in the same compiled module. Distinctness is necessary for the stated maximum atomic weight1/4; coincident translations may not silently retain this weight.

### Shmerkin2019, Theorem9.2: analytic-family L2 densities

Module: `Lean/LambdaCantor/First/LinearRegularityExternal.lean` (source-only pending compilation).
Declaration: `LambdaCantor.First.LinearRegularity.shmerkin2019_theorem92_uniform_l2`.
Primary source: same2019 Annals paper, Theorem9.2, printedp385, links above. Primary statement reread by linear implementation agent2026-10-21.
Exact specialization: two real parameters on an open preconnected domain; finite alphabet cardinality at least2; analytic positive contraction below1 and analytic translations; every distinct pair of actual infinite address sums differs at some parameter. There exists an exceptional parameter set of Hausdorff dimension at most1. At a parameter outside it, distinct translations, reciprocal alphabet cardinality strictly less than contraction (q=2 similarity mass condition), and the actual equal-weight invariant probability law imply a measurable nonnegative real L1-intersect-L2 density representing that measure. No uniform density norm across the parameter domain is asserted. Finite-block coding, collision exclusions and actual invariant-law hypotheses must be proved internally.

### Shmerkin2014, Proposition2.3: Fourier decay outside a contraction exception

Module: `Lean/LambdaCantor/First/LinearRegularityExternal.lean` (source-only pending compilation).
Declaration: `LambdaCantor.First.LinearRegularity.shmerkin2014_proposition23_two_maps`.
Primary source: Shmerkin (2014), Proposition2.3, https://arxiv.org/html/1303.3992v2 . Primary statement reread2026-10-21.
Exact specialization: one Hausdorff-dimension-zero subset of(0,1), independent of the translations; outside it every actual invariant probability law for two distinct real translations with equal positive weights has power decay of its characteristic function at absolute frequency at least1. The positive decay exponent and constant may depend on the measure. The characteristic-function normalization exp(i*x*frequency) is an equivalent frequency scaling of the source normalization. Sparse power-map pullbacks, coordinate independence and convolution consequences are internal obligations; no four-map distinctness is assumed for the sparse projected sum.

### Falconer2003, product formula7.3: real set times an interval

Module: `Lean/LambdaCantor/First/LinearRegularityProduct.lean` (source-only pending compilation).
Declaration: `LambdaCantor.First.LinearRegularity.falconer2003_product73_interval`.
Primary source: Falconer, Fractal Geometry, second edition(2003), product formula7.3/equation7.7, printedp102 (PDFp128); publisher https://doi.org/10.1002/0470013850.ch7 ; checked primary book text https://www.muslimuniversity.edu.af/uploads/library/Fractal.Geometry.Mathematical.Foundations.and.Applications.Second.Edition.eBook-EEn_957.pdf .
Exact specialization: any real set E and ordered real endpoints a<=b satisfy dimH(E times[a,b])<=dimH(E)+1. The source bounds product Hausdorff dimension by first-factor Hausdorff dimension plus second-factor upper box dimension. Lean's max product metric and the Euclidean metric are bi-Lipschitz equivalent. The unbounded real-slope extension by countable interval union and the actual sparse exceptional-set lift are proved internally, not included in the axiom.

### Classical Plancherel for the actual L1 integral Fourier transform

Module: `Lean/LambdaCantor/First/RootsExternalPlancherel.lean` (EXIT0).
Declaration: `LambdaCantor.First.Roots.External.classical_plancherel_l1_l2`.
Checked source: Terence Tao,247B Notes1: Restriction theory,29March2020, introductory equations(1),(3), https://terrytao.wordpress.com/2020/03/29/247b-notes-1-restriction-theory/ .
Exact specialization: a complex-valued real-line function which is Integrable and MemLp2 for Lebesgue measure has its actual VectorFourier integral transform in MemLp2, with equality of integrals of squared norms. Normalization is exp(-2*pi*i*x*frequency), exactly Mathlib's Real.fourierChar with the real inner product. This isolates the standard identification of the L1 integral transform with the L2 transform; it does not assert any nonlinear kernel estimate, density convergence or root-law regularity.

First source scan found no executable sorry/admit/native_decide. Native compiler trust elsewhere is unchanged by these entries. Final verified target-specific axiom dependencies will be reported from real Lean terminal output, not inferred solely from this source list.

Compilation update 2026-10-21 10:01:24UTC: First/LinearRegularityExternal.lean EXIT0, source SHA2567A0E8ACB08E3A2EC672D96CCF33684D06CCB2422BBD0DFA8FDCC17102F9E2304. Its two standard Shmerkin declarations above are now compiled; their actual linear-regularity application and nonlinear root-fibres conclusion remain internal unfinished obligations. Earlier source-only status is superseded only for this module.

Compilation update2026-10-21 10:05UTC: First/LinearRegularityProduct.lean EXIT0. The standard Falconer interval-product input and internal extension to all real slopes / all block powers now compile. This supersedes its earlier source-only status; nonlinear state-measure exclusion still requires the paper-specific inverse-Lipschitz and Frostman application.

## First classical compact-measure Fourier converse (2026-10-21; source pending compilation)
- Planned declaration: `LambdaCantor.First.Roots.External.classical_compact_measure_l2_fourier_density`.
- Exact scope: a finite positive Borel measure on R concentrated on a compact set; its actual characteristic function belongs to L2(volume). Conclusion: it has a measurable nonnegative real density, integrable and in L2, with equality to the actual withDensity measure. Finite Borel measures on R are Radon; positivity and finite total mass supply a nonnegative L1 representative.
- Verified primary research statement: Fernando Román García, *A Fourier Coefficients Approach to Hausdorff Dimension in the Heisenberg Group*, arXiv:1801.09022v3, Theorem 1.2(1), PDF page 2: https://arxiv.org/pdf/1801.09022 ; readable theorem: https://arxiv.org/html/1801.09022 . This is the Euclidean theorem in the introduction, not the Heisenberg generalization. The paper refers to Mattila, *Fourier Analysis and Hausdorff Dimension*, p31 for its proof.
- Source normalization is (2*pi)^(-1/2) times the transform with negative sign. Mathlib charFun uses exp(i*t*x); reflection and multiplication by a nonzero constant preserve L2 membership. No quantitative norm constant is asserted here.
- Why separate: the existing forward Plancherel declaration assumes an L1/L2 density and cannot establish density existence from finite characteristic energy. Compact good energy sublevels can contain exceptional parameters, so density existence must be established at every selected representative. Actual projected-law compact support and weighted-energy-to-L2 implication are internal Lean obligations.
- This is the sixth named First external input, not an axiom for any manuscript root-law or dimension conclusion. No terminal compilation or axiom audit is claimed for its downstream uses yet.


First Fourier converse activation update: `RootsExternalFourierDensity.lean` now contains exactly the declared `LambdaCantor.First.Roots.External.classical_compact_measure_l2_fourier_density`; `RootsFourierDensityInterface.lean` retains its compact-support scope and internal energy reduction. `RootsGoodSetDensities.lean` uses it to remove the representative-density premise. `FourierDensityAudit.lean` is prepared for a real #print axioms check. These new files have not yet compiled; the earlier TrustAudit EXIT0 does not cover this sixth input.

Bibliographic correction to the preceding Fourier-converse entry: Román García's reference [22] is Mattila, *Geometry of Sets and Measures in Euclidean Spaces* (Cambridge, 1995), p31, NOT *Fourier Analysis and Hausdorff Dimension*. The directly checked statement remains Román García Theorem1.2(1); no claim of having checked the cited book page is made. The external declaration and hypotheses are unchanged.

<!-- R025 CURRENT REGISTERS -->

# R025 current registers

Synchronized at 2026-10-27T22:14:41.522875+00:00. The preceding R018 entries retain their historical timestamps and status. These current source registers define possible mathematical trust inputs; only current terminal `#print axioms` output determines which ones a finished theorem uses. Neither source registration nor a generic axiom authorizes replacing an article-specific conclusion.

## EXTERNAL_THEOREMS-R025-First.md

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


## EXTERNAL_THEOREMS-R025-LastAE.md


## Standard forward irrational rotation (Kronecker)

- Lean axiom: `LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation` in `Lean/LambdaCantor/Last/ExternalKronecker.lean`.
- Statement: for irrational real alpha, every real target, epsilon>0 and natural start, there are natural k>=start and integer m with |m-alpha*k-target|<epsilon. No Cantor or Fermat hypotheses/conclusions.
- Primary source checked: John Milnor, Dynamics lecture notes, Chapter IV, section14C, Lemma14.14, PDF page index10 (printed14-11), https://www.math.stonybrook.edu/~jack/DYNOTES/dn14.pdf . Its forward-orbit assertion applies to any initial point; shifting the initial point gives arbitrary start and lifting the target arc gives m.
- Reason for external registration: explicitly authorized standard lemma; Mathlib AddCircle.DenseSubgroup is not cached. The corresponding Mathlib source is Mathlib/Topology/Instances/AddCircle/DenseSubgroup.lean (Yury Kudryashov,2024).
- Internal downstream proofs retained: natural k,m both escaping to infinity, arbitrary phase convergence, and actual near-axis coefficient convergence. Public IrrationalRescaling signatures unchanged. No actual source, positive dimension, or manuscript theorem is axiomatized.
- Status: source frozen, compilation pending. IrrationalRescalingAudit prints downstream axioms; update status only after actual EXIT0.

## General finite-measure Plancherel density criterion

- Lean axiom: `LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density` in `Lean/LambdaCantor/AE/ExternalPlancherelDensity.lean`.
- Exact statement: for an arbitrary finite positive Borel measure `measure` on the real line, if its actual transform `frequency -> integral exp(-2*pi*i*frequency*point) dmeasure(point)` belongs to L2 of Lebesgue measure, there is a real density in L1 and L2, nonnegative almost everywhere, whose density measure is exactly `measure`. The squared physical L2 integral equals the squared Fourier L2 integral, with no normalization constant under the stated 2*pi convention.
- Primary sources checked 2026-10-24: Károly Simon, *Fractals and Fourier analysis*, File C, Theorem 4.3, slide83; slides84–86 give the Mattila proof and identify Mattila2015, Theorem3.3, p31: https://math.bme.hu/~simonk/ff/2017_C_8_uj.pdf . Exact unitary 2*pi normalization: Gautam Iyer, *Lecture Notes on Measure Theory*, Fall2022, section11.3, Theorem11.16, p22, with transform convention in section11.1: https://www.math.cmu.edu/~gautam/sj/teaching/2022-23/720-measure/pdfs/measure-tablet.pdf . Publisher record for the cited Mattila chapter: https://doi.org/10.1017/CBO9781316227619.004 .
- Source-to-formal specialization: dimension one; finite positive measures specialize the finite Borel criterion. Positivity of the measure makes the density nonnegative, and finiteness makes it integrable. Plancherel gives the exact norm identity. There is no parameter, Cantor, convolution, annulus, Newton, root-family, or dimension input in this axiom.
- Authorization: the user explicitly allowed precisely sourced known external general analytic tools during R025; the parent approved this exact criterion before source creation.
- Status: new optional module, source only. No active dependency-path replacement has yet been made. Existing internal Riesz/Plancherel constructions are preserved.
- Activation update: after the parent recorded the approved 18-module density-path delta in the shared project status, `AffineSobolevDensity` and `InitialKernelL2` were switched to the classical conditional-density route. Public declaration names and statements are retained. The original Riesz source modules are unchanged. `ClassicalDensityAudit.lean` checks the expected added finite-measure criterion axiom in both conditional conclusions; the source is unverified until the serial compiler and audit succeed.
- Pure definitions were separated from actual averaging: `FourierEnergyDefinition.lean` defines `fullFourierEnergy` and proves elementary Fourier measurability; the original modules reexport the same names. `FullFourierEnergy` still retains the real parameter-averaging proof imports and obligations. Thus the conditional density can be tested without assuming or deleting the manuscript's averaging estimate.

## Converse Plancherel for an actual complex L1 Fourier transform

- Lean axiom: `LambdaCantor.AE.ExternalPlancherel.complex_L1_of_fourier_L2` in `Lean/LambdaCantor/AE/ExternalPlancherelDensity.lean`.
- Exact statement: if an arbitrary complex function on the real line belongs to L1 and its actual integral Fourier transform with the 2*pi convention belongs to L2, then the original function belongs to L2 and its squared L2 integral equals the transform's squared L2 integral.
- Primary source: Iyer2022, section11.3, Theorem11.16 (bijective linear L2 isometry) together with section11.2, Theorem11.10 (inversion), at the same official CMU PDF linked above. This is the standard converse corollary: the inverse L2 transform of the given L2 transform is identified with the original L1 function by Fourier inversion and uniqueness.
- Scope: arbitrary complex L1 functions, with no support, parameter, Cantor, convolution, smoothing, root, or dimension assumptions. This may shorten the generic signed-Riesz verification path; it does not assume any manuscript interpolation estimate.
- Status: optional source only, not yet used by an active analytic module. Existing signed-Riesz source is preserved. Any active path change and downstream axiom audit must be recorded separately.

### R025 activation: generic signed Plancherel specialization in transport

Parent authorization and prior shared-status activation notice recorded before this change (2026-10-24, approximately 17:11 UTC). `ClassicalSignedDensity.classical_signed_density_memLp_and_norm_bound` specializes only the already registered general `ExternalPlancherel.complex_L1_of_fourier_L2` statement to real signed integrable functions. `SobolevTransportMollification` now calls that specialization. All actual mollifier Fourier-error, smoothing, coupling, support and scalar interpolation proofs remain formal obligations. Original `SobolevTransportSignedRiesz` and its public declarations remain in source unchanged.

The expected external analytic axiom in `ClassicalTransportAudit` is `LambdaCantor.AE.ExternalPlancherel.complex_L1_of_fourier_L2`; the separately activated affine density path retains `LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density`. No averaged-Sobolev, pair-annulus, Newton-error, root, or dimension theorem was registered. This activation is source only pending dependency-ordered compilation and axiom audit.

## Generic Newhouse Gap Lemma for binary defining sequences

- Declaration: `LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma` in `Lean/LambdaCantor/Last/ExternalNewhouseBinary.lean`.
- Primary source directly inspected: S. E. Newhouse, *The abundance of wild hyperbolic sets and non-smooth stable sets for diffeomorphisms*, Publ. Math. IHES 50 (1979), printed pp.106–108, definition of defining-sequence thickness, Lemma 4 and Remark 2. https://numdam.org/item/PMIHES_1979__50__101_0.pdf (PDF pages 6–8, zero based).
- Exact formal assumptions: two arbitrary sets of reals have explicit full binary closed-interval constructions; every node has positive width; children retain the outer endpoints and have a strict positive separating gap; the actual set equals the intersection of all finite-level unions; the interval mesh tends uniformly to zero. Each left and right child width is at least a positive bound times its node gap. The product of the two positive bounds exceeds one. Neither set lies in an order-connected subset of the other's complement, including unbounded complementary intervals.
- Conclusion: the two arbitrary sets intersect. There is no dimension conclusion, no Fermat or power/log family, and no contraction parameter in the external declaration.
- Formulation correspondence (general standard defining-sequence specialization): enumerate the finite binary node gaps ancestor first. Endpoint coherence and the strict children show these are disjoint removed gaps; exact limit equality and vanishing mesh show they exhaust the complement and give nonempty compact perfect Cantor limit sets. At a gap's removal the two adjacent bridges are the immediate children, so the explicit bounds lower-bound defining-sequence thickness. Newhouse defines set thickness as the supremum over defining sequences, with no size-order requirement. Apply Lemma 4; Remark 2 deletes the closed-gap requirement for intersection alone. The stronger finite-stage interior conclusion is deliberately absent.
- Trust boundary: only the classical general Gap Lemma is external. Actual logarithmic cylinder endpoints, exact represented set, mesh, bridge bounds, complementary-gap noncontainment, circle-gap counting and endpoint intersection witnesses must be supplied by internal Lean proofs. No such application is yet compiled or claimed.
2026-10-26 declaration-check update: ExternalNewhouseBinary.lean SHA2568266F5E0259ED231C786A9AA2DD0409F3754847C3AF42D31029303EB953E3572 actual serial compiler EXIT0 END2026-10-26T09:01:45.5135681Z (22.0675047s). Missing explicit Mathlib.Data.Real.Basic import was repaired; external proposition unchanged. This verifies declaration elaboration ONLY. Actual binary presentations/application/coarse theorem and downstream axiom audit remain pending; no upgrade to proved-paper status.

### 2026-10-27T04:37:33.8799028Z activation notice: literal Section4.7 Sobolev density wrapper

The newly integrated manuscript4.7 wrapper imports SobolevDensity and therefore AlmostEverywhereDensity. Before changing that active path, the LastAE parent authorizes this exact reuse of the ALREADY REGISTERED general ExternalPlancherel.finite_measure_L2_density proposition (same primary Simon/Mattila/Iyer sources and exact statement above). No new external proposition or internal manuscript conclusion is registered. AlmostEverywhereDensity retains all three public statements byte-for-byte; its generic exists_integrable_measure_L2_density proof simply takes the L1, L2, positivity and measure-identity components of the registered general finite-measure criterion, discarding its norm identity. The other two proofs remain unchanged.

Read-only source graph delta verified by AE owner before activation: replace ConvolutionDensity import by ConvolutionFourierL2 plus ClassicalDensityCore, keep ParameterCutoffCover. Local closure68 becomes60: remove10 old density-only modules (BoundedMeasureFunctional, ClosedBallSmoothApproximation, ConvolutionDensity, FourierTestDuality, FourierTestSubspace, MeasureFourierDuality, RepresentativeBallIntegrals, RepresentativePositivity, RieszConvolutionRepresentative, SmoothTestFourier), add ClassicalDensityCore and ExternalPlancherelDensity. All60 new-closure modules already occur in the active ActualDimensionTerminal graph; no new actual averaging/transversality/root/Newton/freezing conclusion is assumed. Old ConvolutionDensity and all Riesz source files remain unchanged. Source activation is not compiler acceptance; SobolevDensity and manuscript4.7 actual axiom audits must include the registered finite-measure criterion when used.

### 2026-10-27T05:04:32.1748069Z actual conditional-density application audit

ClassicalDensityAudit.lean SHA2565C3EC8959EE68A6FB94779168397E794204320CCEB45B7DA3BCD9DB35DAD7F57 compiled EXIT0, END2026-10-27T05:03:48.6421862Z (48.9832598s). Actual printed axiom lists for exists_common_affineSobolev_density and exists_affine_density_sharp_L2 are EXACTLY propext, Classical.choice, Quot.sound, and LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density. The Fourier density/measure identity is standard3 only. No complex converse, cylinder-extension, internal target, native or sorry axiom occurs in these three dependencies. All current-source application modules in this small chain now have canonical SHA/END/EXIT0. This verifies the previously registered conditional affine-density use; it does not certify the actual averaged energy, nonlinear centered kernel, L1 limit, full almost-everywhere dimension theorem, or new4.7 wrapper (those remain queued separately).

### 2026-10-27 actual analytic exception and irrational application audit

AnalyticSourcesAudit.lean SHA25682CC89B566DB6DEB0CBB4C1C99E8C789E23E43811392A81086B85B02E52E3A70 compiled EXIT0, END2026-10-27T14:28:06.7223938Z (48.8107395s). All eleven printed lists were read in full. two_band_affine_strict_overlap, two_band_closed_central_strict_returns, two_band_local_source_criterion and two_band_positive_derivative_criterion use exactly propext, Classical.choice and Quot.sound. real_zero_phase_depth_sequences, power_endpoint_source_positive_dimension, logarithmic_endpoint_source_positive_dimension, analytic_cubic_last_strict_upper, analytic_quadratic_last_strict_upper, analytic_three_halves_last_strict_upper and analytic_irrational_last_strict_upper use exactly those three plus the already registered general ExternalKronecker.forward_integer_difference_approximation. Its precise statement and primary Milnor source remain as registered above; no external proposition is added here. No native, sorryAx, internal conclusion or unregistered axiom appears in these lists.

The strict Section4 source-closure verifier checked2026-10-27T14:28:40Z accepts the analytic-irrational and analytic-exceptions groups with all current local SHA/END/EXIT0 dependencies. This does not establish the coarse analytic input, universal strict bound, endpoint persistence, actual nonlinear centered kernel, a.e. exact dimension or full manuscript Section4 entry; these still require their queued actual proofs and audits.

### 2026-10-27 actual four-orientation endpoint application audit

EndpointTransferAccepted.lean SHA2563866B575113A569FC54CC0025C052101D109178967C6478CADEF1B2F065D1720 compiled EXIT0, END2026-10-27T14:31:03.6644592Z. EndpointTransferCompleteAudit.lean SHA25625E6394956B9C6437EA38D9F64CF0C694F9E8FB4FF508C743FB581AD98D00EAA compiled EXIT0, END2026-10-27T14:32:17.0886125Z (45.6335883s). All five actual printed lists were read. two_band_separable_c1_criterion and two_band_positive_derivative_criterion_reciprocal use exactly propext, Classical.choice and Quot.sound. power_endpoint_source_reciprocal_positive_dimension, logarithmic_endpoint_source_reciprocal_positive_dimension and endpoint_source_positive_dimension use exactly those three plus the already registered general ExternalKronecker.forward_integer_difference_approximation. No native, sorryAx, internal conclusion or unregistered axiom appears. No new external proposition is introduced. Endpoint persistence and full Section4 integration are separate pending checks.

### 2026-10-27 actual endpoint persistence audit

EndpointTransferPersistence.lean SHA256 DD9A6C8E3A00192C65BC3001D1CFC58D226BB4F18BF6C58F2F62CB838199C9CB compiled EXIT0, END2026-10-27T14:54:10.2524475Z (35.1164785s). Its two print commands are outside the namespace so the output records full axiom names without abbreviation. endpoint_accepted_source_persists uses exactly propext, Classical.choice and Quot.sound. endpoint_source_positive_dimension_neighborhood uses exactly those three plus the already registered general LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation. Both current source-closure records are accepted by section4_acceptance.py at14:56. The earlier failed recovery prints containing sorryAx are superseded; they were never accepted. No proof statement, trust allowlist, external proposition or heartbeat option was changed by the display adjustment.

### 2026-10-27 actual open-phase C1 isolation audit

AnalyticIsolatedActualC1.lean SHA256 F184D38524F1671BCB534D6C7A4866C069A4CF768FD931BBD9076E0B6EE57B62 compiled EXIT0, END2026-10-27T15:44:20.1167252Z (30.6852094s). AnalyticIsolatedActualC1Audit.lean SHA256 B0AF2AA7DB80EE8761E17F68BEA3C1B4A2057C3DF91FED46BB94667EB4A143FF compiled EXIT0, END2026-10-27T15:45:17.1159388Z (27.2088908s). Its three actual printed dependencies for open_phase_isolated_strict_address_eventually_periodic, open_phase_isolated_strict_address_in_parameterField and open_phase_isolated_c1_point_in_parameterField are exactly propext, Classical.choice and Quot.sound. No external theorem, native axiom, sorryAx, internal conclusion axiom or unregistered proposition appears in these three lists. This records an internal proof application, not a new external result. Critical C2 and actual rational Fermat isolation audits remain separate pending checks.

### 2026-10-27 actual open/critical C2 isolation audit

AnalyticIsolatedActualPoints.lean SHA256 51E4D1B1C993C00DDA5CCA583805BFFBF48F3521CD95F9D2815A3E97FC2EAC3B compiled EXIT0, END2026-10-27T15:47:09.8301397Z (29.9699892s). AnalyticActualIsolationAudit.lean SHA256 439AA29B47D3807705967424C0B0E59229EC5B87C3EAB0884A1FE30785E744B2 compiled EXIT0, END2026-10-27T15:49:53.8508510Z (27.6128036s). Complete actual printed footprints: open_phase_isolated_c2_point_in_parameterField uses exactly propext, Classical.choice and Quot.sound; critical_isolated_c2_point_in_parameterField uses exactly those three plus the already registered generic LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering. No Mordell, native, sorryAx, internal conclusion or unregistered axiom appears in these two lists. The primary Adamczewski–Bugeaud source and exact general Pisot-stammering statement remain as registered above; no new external proposition is introduced. Actual rational Fermat isolation and the universal strict bound require the subsequent finite-generation/Mordell and return assemblies, still unverified here.

### 2026-10-27 actual rational Fermat isolation audits

RationalLastActualIsolationAbove.lean104459325C114AD626FE2C0E1433A2276113485F77C199521972CEB466A1B159 passed END15:58:16.8715189Z. AboveAudit2E333BA0E5822239726B16D24D3E213D385EE166C9DA76E1A9863984A9B9A1CB passed END15:59:59.0562986Z. Actual coordinate classification above the critical ratio uses exactly standard3; actual isolated-point finiteness above critical uses standard3 plus registered External.mordell_smooth_plane_curve only.

RationalLastActualIsolationNormalized57FB2CAA491631FDF1D0FDDA2D6FDE2137993DB5C41CB3ACC8843BCA1646F318 passed END16:01:28.1568211Z. ActualIsolationFermat passed END16:02:54.8235474Z. ActualIsolationAudit387B051C1AF6C2680D5A615FD073A02C060C55DC37DD91D7D137E52983122CC8 passed END16:03:51.3129983Z (28.2522039s). Its four actual lists were read completely: exists_actual_fermat_prefix_normalization and normalizedFermatPrefix_isolated_pullback are exactly standard3; actual_rational_fermat_isolated_coordinates_at_critical is standard3 plus the registered general AB Pisot-stammering result; finite_isolated_actual_rational_intersection_at_critical is standard3 plus that result and the registered general Mordell theorem. No native, sorryAx, internal conclusion or unregistered axiom occurs. No external proposition is added here. The strict full local source-closure verifier at16:06 accepts the analytic-isolated group including these actual discharges; full Section4 still requires coarse/returns/universal and AE/manuscript integration.


### 2026-10-27T16:50:21.015383+00:00 universal strict last bound: complete actual terminal receipt
Frozen manuscript commit:429d53bb243f49b19ba8169de0e82ed70050ec7f. Public theorem: `LambdaCantor.Last.universal_lastTransition_lt_critical {exponent : ℝ} (hexponent : 1 < exponent) : lastTransition exponent < (Real.sqrt 3 - 1) / 2`. No caller hypotheses beyond the real exponent being greater than one; reduced rational representation, three small exceptional cases, actual infinitude, actual finite isolation and return persistence are discharged internally. This does not certify the separate a.e. dimension/Sobolev/sqrt2 pipeline or integrated Section4 entries.

**RationalLastStrictAudit.lean** SHA256 `85C2530D352501C4D0C36405DA3429C25F831F9D7D7BBF21FFD1176F2F60C7BB`, END_UTC `2026-10-27T16:26:21.3515909Z`, EXIT0. Every actual printed list:
- `LambdaCantor.Last.selected_perfect_actual_fermat_normalization`: `propext, Classical.choice, Quot.sound`.
- `LambdaCantor.Last.strict_return_criterion_persist_parameter`: `propext, Classical.choice, Quot.sound`.
- `LambdaCantor.Last.joint_strict_derivative_moving_cylinder_error`: `propext, Classical.choice, Quot.sound`.
- `LambdaCantor.Last.perfect_fibre_positive_dimension_persist_parameter`: `propext, Classical.choice, Quot.sound`.
- `LambdaCantor.Last.actual_fermat_positive_dimension_persist_of_infinite_of_finite_isolated`: `propext, Classical.choice, Quot.sound`.
- `LambdaCantor.Last.rational_positive_dimension_at_or_above_critical_of_infinite`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering, LambdaCantor.Last.External.mordell_smooth_plane_curve`.
- `LambdaCantor.Last.rational_lastTransition_lt_critical_of_infinite_intersections`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering, LambdaCantor.Last.External.mordell_smooth_plane_curve`.

**AnalyticCoarseConclusionAudit.lean** SHA256 `7F74D6846092BDF95717E766CF99C4471FBA453BFE4A1761CE407E96AD6DCC3B`, END_UTC `2026-10-27T16:28:26.7366312Z`, EXIT0. Every actual printed list:
- `LambdaCantor.Last.coarse_strict_log_link_all_exponents`: `propext, Classical.choice, Quot.sound`.
- `LambdaCantor.Last.coarse_rational_infinite_intersection`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma`.
- `LambdaCantor.Last.rational_lastTransition_lt_critical`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering, LambdaCantor.Last.External.mordell_smooth_plane_curve, LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma`.

**UniversalLastAudit.lean** SHA256 `744BB607CE407DBD48153859776E245F22A4AFCB0974270595C156A97637E1D5`, END_UTC `2026-10-27T16:34:33.4885358Z`, EXIT0. Every actual printed list:
- `LambdaCantor.Last.analytic_irrational_last_strict_upper`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation`.
- `LambdaCantor.Last.analytic_quadratic_last_strict_upper`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation`.
- `LambdaCantor.Last.analytic_cubic_last_strict_upper`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation`.
- `LambdaCantor.Last.analytic_three_halves_last_strict_upper`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation`.
- `LambdaCantor.Last.coarse_strict_log_link_all_exponents`: `propext, Classical.choice, Quot.sound`.
- `LambdaCantor.Last.coarse_rational_infinite_intersection`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma`.
- `LambdaCantor.Last.rational_lastTransition_lt_critical`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering, LambdaCantor.Last.External.mordell_smooth_plane_curve, LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma`.
- `LambdaCantor.Last.universal_lastTransition_lt_critical`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering, LambdaCantor.Last.External.mordell_smooth_plane_curve, LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation, LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma`.

**UniversalLastPositivity.lean** SHA256 `7C92E3128878161A7E6CF9D12CB68BA9B4F8367DF5FF8FF603C307C2ED334A6E`, END_UTC `2026-10-27T16:41:02.6105479Z`, EXIT0. Every actual printed list:
- `LambdaCantor.Last.positive_dimension_above_lastTransition`: `propext, Classical.choice, Quot.sound`.
- `LambdaCantor.Last.universal_positive_dimension_at_or_above_critical`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering, LambdaCantor.Last.External.mordell_smooth_plane_curve, LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation, LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma`.
- `LambdaCantor.Last.universal_positive_dimension_near_critical`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering, LambdaCantor.Last.External.mordell_smooth_plane_curve, LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation, LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma`.

The universal strict theorem uses exactly the three ordinary Lean foundations plus these FOUR already registered generic classical inputs, and no others:
- Kronecker forward irrational approximation: Milnor, Dynamics notes IV14C, Lemma14.14, https://www.math.stonybrook.edu/~jack/DYNOTES/dn14.pdf .
- Adamczewski–Bugeaud, Annals165 (2007), Theorem5 pp553–554, the precisely registered Pisot/exact-double stammering specialization: https://annals.math.princeton.edu/wp-content/uploads/annals-v165-n2-p04.pdf . Exact Lean statement and source check: EXTERNAL_SOURCE_CHECKS-R025-Root.md.
- General Mordell over finitely generated characteristic-zero fields, smooth plane-curve specialization: Jarden–Razon, Proposition5.2, https://www.math.tau.ac.il/~jarden/Articles/paper60.pdf . Exact Lean statement and source check: EXTERNAL_SOURCE_CHECKS-R025-Root.md.
- Generic Newhouse binary defining-sequence gap lemma with actual bridge/thickness/linking hypotheses: Newhouse1979 printed pp106–108, Lemma4/Remark2, https://numdam.org/item/PMIHES_1979__50__101_0.pdf . Exact statement and scope are registered earlier in this file.
No internal paper conclusion, Fourier-density/projection input, native axiom, sorryAx or unregistered theorem occurs in the universal strict theorem's actual footprint. The five purely geometric/normalization return heads use only standard3; the exact per-head differences are recorded above. No new external proposition is introduced by this receipt.
UniversalLastPositivity's only post-pass modification was adding these three diagnostic print commands outside its namespace; all theorem bodies/signatures are unchanged, the new SHA has now itself compiled EXIT0, and all three printed footprints are recorded above. UniversalLastConclusion and UniversalLastAudit remain frozen at their accepted SHAs.


2026-10-27T18:55:34.683897+00:00 Actual norm-convention comparison receipt (no new external proposition)
Sole scope: all real regularity>=0 and every real frequency, including both zero endpoints; standardWeight <= 2^regularity * implementedWeight and implementedWeight <= 2 * standardWeight. Constants are independent of ratio/frequency. This does not alone prove averaged Sobolev4.7 or canonical compact integrability.

UTC=2026-10-27T18:52:36.4796208Z MODULE=LambdaCantor/AE/SobolevWeightComparison.lean SHA256=8DF52E47CB9C80506BB82D0E7A3A78A934A789E45C609D9F8555ECCDA296F625
'LambdaCantor.AE.sobolev_weight_comparison_standard_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.sobolev_weight_comparison_implemented_le' depends on axioms: [propext, Classical.choice, Quot.sound]
ELAPSED_SECONDS=35.4056241 END_UTC=2026-10-27T18:53:11.8879452Z
EXIT=0



2026-10-27T19:59:50.763786+00:00 Actual canonical and averaged Sobolev core: complete15-list receipt
Scope: actual Cantor self-convolution, actual nonnegative L1-and-L2 density, exact density/measure Fourier identity, canonical weight(1+abs(frequency)^2)^regularity; every compact subset of an admissible interval has finite extended-valued canonical parameter energy and integrable toReal. Conditions0<lower<=upper<1/2, regularity>=0 and exact2*regularity<2*log(8/3)/log(upper/lower^3)-1. Old extended parameter integral is recovered from independently proved AE energy<top before integrable_toReal_iff; infinity.toReal cannot hide an infinite parameter-energy contribution. These are core conclusions; the literal wrapper and all Section4/integrated entries still need their actual certificates.
Every comparison/compact-integral head uses exactly standard3. The AE density heads add ONLY the already registered generic ExternalPlancherel.finite_measure_L2_density, whose precise finite-measure/Fourier-L2 statement and sources are in the existing external registers/AE/ExternalPlancherelDensity.lean. No new external proposition/native/sorry/internal-paper conclusion axiom.

UTC=2026-10-27T19:52:37.2280450Z MODULE=LambdaCantor/AE/CanonicalSobolevEnergy.lean SHA256=450C9BA5DB8B478B35B58D46623634DA57DD06021A200443EA2C537FA322971A
'LambdaCantor.AE.canonicalSobolevEnergy_le_fullFourierEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.fullFourierEnergy_le_canonicalSobolevEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.lintegral_canonicalSobolevEnergy_compact_subset_lt_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LambdaCantor.AE.integrableOn_canonicalSobolevEnergy_compact_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LambdaCantor.AE.ae_hasCanonicalSobolevDensity_on_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density]
ELAPSED_SECONDS=47.9860456 END_UTC=2026-10-27T19:53:25.2191566Z
EXIT=0


UTC=2026-10-27T19:54:20.5240684Z MODULE=LambdaCantor/AE/AveragedSobolevAudit.lean SHA256=A7778A272218BF2785D5DD58E4A8E100199CADEBE2B69B07D97EE407DE4D5482
'LambdaCantor.AE.lintegral_cutoff_fullFourierEnergy_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.locallyIntegrableOn_fullFourierEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.fullFourierEnergy_eq_convolution_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.fourier_density_eq_measureFourier' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.ae_hasSobolevDensity_on_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density]
'LambdaCantor.AE.canonicalSobolevEnergy_le_fullFourierEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.fullFourierEnergy_le_canonicalSobolevEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.lintegral_canonicalSobolevEnergy_compact_subset_lt_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LambdaCantor.AE.integrableOn_canonicalSobolevEnergy_compact_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LambdaCantor.AE.ae_hasCanonicalSobolevDensity_on_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density]
ELAPSED_SECONDS=41.0337524 END_UTC=2026-10-27T19:55:01.5600530Z
EXIT=0



Literal frozen Lemma4.7 independent wrapper accepted receipt; exactstatementB84 scope ownerchecked against frozenmain.tex2201-2208. Diagnostic-only namespace relocation from7EF preserves proof/statement; newactualfullqualified footprint (no whitelist relaxation):
UTC=2026-10-27T20:15:57.1971587Z MODULE=LambdaCantor/Manuscript/AverageSobolev.lean SHA256=BD27FC7C8B1A00222AF21B4364C4427DD950A4092E9F3987B7162575A7DCE6BC
'LambdaCantor.Manuscript.average_sobolev' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density]
ELAPSED_SECONDS=32.0497597 END_UTC=2026-10-27T20:16:29.2684100Z
EXIT=0

Full16group goal andcompleteSectionFour/fivehead totalentry stillrequired; this receipt alone does not certifyAEexactdimension orsqrt2.


## EXTERNAL_SOURCE_CHECKS-R025-Root.md

# R025 primary-source checks by root

These checks validate the scope of registered external inputs, not completion of a manuscript-specific consequence.

- Adamczewski–Bugeaud, Annals 165 (2007), Theorem 5, printed pp.553–554: https://annals.math.princeton.edu/wp-content/uploads/annals-v165-n2-p04.pdf . The primary PDF was read on 2026-10-24. It covers bounded sequences of rational integers in Pisot or Salem bases satisfying Condition (*) with repetition exponent greater than one. The registered Pisot/exact-double specialization retains nonperiodicity, increasing repeated-word lengths and a bounded prefix/word ratio. Index zero instead of one rescales by the nonzero algebraic base, which preserves both generated-field membership and transcendence.
- Milnor, Dynamics notes, Lemma 14.14: https://www.math.stonybrook.edu/~jack/DYNOTES/dn14.pdf . The primary PDF explicitly states forward irrational rotation orbits are dense. Dropping a finite prefix gives the arbitrary starting-index form in the registered Kronecker input; translating the target and lifting circle distance gives the integer correction.
- Jarden–Razon, paper60, Proposition 5.2: https://www.math.tau.ac.il/~jarden/Articles/paper60.pdf . For a finitely generated field and an absolutely irreducible curve of genus at least two, without a finite-field model, rational points are finite. Characteristic zero makes the finite-field exception automatic. The registered smooth plane curve of degree at least four is a standard specialization; the manuscript's particular Fermat curve and arithmetic descent are internal obligations.
- The generic measure-Fourier definitions use Real.fourierChar at minus frequency times value; this is the standard 2π normalization. The Plancherel and L2-density registrations concern generic measures/functions and do not assume a Cantor fibre conclusion.
- Root independently reread Roman Garcia, arXiv1801.09022v3, introduction Theorem1.2(1), on 2026-10-24: https://arxiv.org/html/1801.09022 . It explicitly gives an L2 density for every compactly supported finite positive Radon measure whose Euclidean Fourier transform is in L2. The displayed Fourier convention differs by a nonzero frequency scaling and constant from charFun, which preserves L2 membership. The paper's bibliography entry[22] is Mattila1995, Geometry of Sets and Measures in Euclidean Spaces; the previous secondary attribution to the later Fourier Analysis book was inaccurate. This check relies directly on the displayed primary theorem; it does not independently verify the cited book page31.

The full terminal trust audit must still show which registrations are actually reachable from the final article theorems. Unused historical registrations are not automatically part of that final dependency set.

## Exact Lean declaration registration: bounded stammering series

- Lean axiom: `LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering`.
- Module: `Lean/LambdaCantor/Last/ArithmeticDigitTheorem.lean`.
- Primary theorem: Adamczewski–Bugeaud, Annals of Mathematics165 (2007), Theorem5, pp.553–554, https://annals.math.princeton.edu/wp-content/uploads/annals-v165-n2-p04.pdf . This is the precisely scoped specialization checked above, not a new external result.
- Exact signature:

```lean
axiom adamczewski_bugeaud_pisot_stammering
    (base : ℝ) (pisot : PisotSeriesBase base) (digits : ℕ → ℤ)
    (bounded : ∃ bound : ℕ, ∀ index, |digits index| ≤ (bound : ℤ))
    (stammering : DoubleStammering digits) :
    integerDigitSeries base digits ∈ parameterField base ∨
      Transcendental ℚ (integerDigitSeries base digits)
```

`PisotSeriesBase` explicitly requires a real algebraic integer greater than one with every other complex conjugate strictly inside the unit circle. `DoubleStammering` retains nonperiodicity, unbounded repeated-word lengths, bounded prefix/word-length ratio and two consecutive copies. `parameterField base` is the field generated over the rationals by the base; the series starts at index zero. The manuscript's boundary Pisot property and actual digit-sequence hypotheses are internal Lean obligations.

## Exact Lean declaration registration: smooth plane-curve finiteness

- Lean axiom: `LambdaCantor.Last.External.mordell_smooth_plane_curve`.
- Module: `Lean/LambdaCantor/Last/ArithmeticMordell.lean`.
- Primary theorem: Jarden–Razon, *Pseudo algebraically closed fields over rings*, Israel Journal of Mathematics86 (1994), Proposition5.2, https://www.math.tau.ac.il/~jarden/Articles/paper60.pdf . The general finitely generated characteristic-zero field theorem, the standard smooth plane-curve genus formula and the affine-chart injection give the registered specialization.
- Exact signature:

```lean
axiom mordell_smooth_plane_curve
    (field : Subfield ℝ) (generators : Set ℝ) (finite_generators : generators.Finite)
    (generated : field = Subfield.closure generators)
    (polynomial : MvPolynomial (Fin 3) ℝ) (degree : ℕ) (degree_large : 4 ≤ degree)
    (coefficients : ∀ monomial, polynomial.coeff monomial ∈ field)
    (smooth : SmoothHomogeneousPlanePolynomial polynomial degree) :
    {point : ℝ × ℝ | point.1 ∈ field ∧ point.2 ∈ field ∧
      MvPolynomial.eval ![point.1, point.2, (1 : ℝ)] polynomial = 0}.Finite
```

`SmoothHomogeneousPlanePolynomial` requires degree homogeneity and projective nonsingularity over the complex numbers: every nonzero complex homogeneous zero has a nonzero partial derivative. The degree at least four condition gives genus at least three. The actual Fermat polynomial, its coefficients and nonsingularity, finite field generation and the manuscript's descent/coordinate arguments remain internal proofs. Neither declaration assumes the paper's dimension, transition or source conclusions.


## Root actual universal last-transition audit 2026-10-27T16:42:04.902269+00:00

Frozen paper429d53, Theorem4.2: Last.universal_lastTransition_lt_critical has only exponent:Real and exponent>1 as public input, with conclusion lastTransition exponent<(sqrt3-1)/2. ActualConclusion B5BBA1C4967944527C1010A60D0C7B98EB6E8692610B01BB918AA0017E3E0E3D END2026-10-27T16:33:24.8662270Z EXIT0; actualAudit744BB607CE407DBD48153859776E245F22A4AFCB0974270595C156A97637E1D5 END16:34:33.4885358Z EXIT0. All8printed lists read completely byRoot; independent section4_acceptance at16:37:41.768511Z accepted this exact declaration, both current source closures and all prints, with no unregistered axiom. Final footprint exactly propext, Classical.choice, Quot.sound plus existing general registered External.adamczewski_bugeaud_pisot_stammering, External.mordell_smooth_plane_curve, ExternalKronecker.forward_integer_difference_approximation and ExternalNewhouse.binary_defining_sequence_gap_lemma. No new external proposition/source is introduced; the primary sources and exact general hypotheses are the existing LastAE entries. No native/sorry/internal-paper conclusion axiom. The first4audit heads use standard3+Kronecker, the coarse strict log link standard3 only, rational infinitude standard3+Newhouse, rational bound standard3+AB/Mordell/Newhouse. Actual rational representation, geometric/source/strict-return premises are discharged internally. This is pointwise strict in exponent, not a uniform positive gap. Remaining AE/Sobolev/sqrt2 and integrated manuscript acceptance are unproved by this result. Full strictreadback is in STATUS-Root, with source/canonical logs in the same R025 archive.


## Actual two-branch middle-third endpoint acceptance — 2026-10-27T20:15

Root independently read the exact two typed public endpoints and both complete fully qualified outputs. Audit source D9A567360FD8025200AA4165D3DE1ADAC7DAE491A4338B0F0677EEB004A88CCA, actual END 2026-10-27T20:15:26.3935626Z. Complete139-module current source/SHA/END/EXIT0/artifact/dependency closure accepted with zero failures. Receipt: certificates/rational-analytic/actual-acceptance.json.

Scope: at lambda=1/3, every irrational real exponent>1; and every reduced rational p/q>1 with q>=110. These public types have no caller certificate, source existence or perfectness premise. Low-denominator partition, integer/tail catalogues, full raw production and complete Theorem3.1/article remain obligations. No new external proposition is introduced. All external inputs below are already precisely registered general results; the one finite native computation has user authorization.

```text
'LambdaCantor.RealPowers.irrational_real_power_positive_dimension' depends on axioms: [propext,

 Classical.choice,

 Quot.sound,

 LambdaCantor.External.rational_of_eventually_periodic_digits,

 LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation]

```

```text
'LambdaCantor.RationalPowers.large_denominator_rational_positive_dimension' depends on axioms: [propext,

 Classical.choice,

 Quot.sound,

 LambdaCantor.External.rational_of_eventually_periodic_digits,

 LambdaCantor.External.wiles_fermat_last_theorem,

 LambdaCantor.RationalPowers.denominatorSources_checked._native.native_decide.ax_1_1]

```

The first namespace-relative display attempt was rejected by the strict unchanged registry, preserved as a PASS source/log pair, and reprinted outside the namespace. Neither proof, signature, axiom allowlist nor external statement changed.
