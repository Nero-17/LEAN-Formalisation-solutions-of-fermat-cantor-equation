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
