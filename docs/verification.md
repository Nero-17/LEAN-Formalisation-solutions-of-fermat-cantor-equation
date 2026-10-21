# What the verifiers establish

This is a guide to the finite checks, not a replacement for the paper's proofs.
The predicates below are evaluated using integers or rational intervals. Decimal
values in reports are informational; they do not determine acceptance.

## Polynomial exclusions

`r008_evidence_gap_family.py` expresses each relevant polynomial on the rational
parameter interval in its Bernstein basis and proves every coefficient positive.
Since Bernstein basis functions are nonnegative and sum to one, this certifies
the strict inequality throughout the parameter interval. The all-scale reduction
from those inequalities is supplied in the unit-circle proof.

The cubic and quartic checkers verify each signed residual on the entire Cantor
cylinder and establish that the prefix leaves cover the paired address tree
without overlap. They also check the elementary inequalities used to discard the
remaining scale classes. They do not infer zero dimension from finite survival
counts.

## Digital graphs

`r003_digits_verify.py` enumerates all 4⁵ digit words. It pulls every exclusive
domain back to the initial level, intersects rational linear inequalities in the
slope, and checks exact agreement with the supplied edge set. Vertex ranks must
be nondecreasing on edges; all edges within one rank follow the listed disjoint
simple cycles. This proves eventual periodicity for graph paths. The argument
that vanishing nonlinear errors eventually obey this graph remains in the paper.

## Binary returns

For each of n = 9, 10, 23, 25, 28, 31, 32, 78, 82, the independent checker
reconstructs all one-return and two-incomparable-return intervals using closed
endpoint events, including singleton overlaps. It verifies the full endpoint
hash, the target coverage and the amplified nonlinear-error margin. The compact
certificates are sufficient because the verifier reconstructs the omitted lists.
The separate source-transfer verifier checks the selected covering intervals for
n = 9 and n = 10 after the complete reconstruction. This release uses the compact
certificates instead of duplicating hundreds of megabytes of reconstructible
endpoint lists; the packaging adaptation is recorded in the source manifest.

This computation supplies bounded, robust binary returns. The infinite nested
construction and the resulting Hausdorff dimension estimate are mathematical
steps in the paper, not a conclusion from mere uncountability.

## Weighted returns for the original circle

The source certificate is
`branching_r010_adaptive_B_57_50_theta2.json`, with SHA-256
`c25b7844a9b9340ae412b7a51a1534865d436580b003ee9664a64fb9442afd83`.
The independent verifier checks all 232304 partition intervals, valid ternary
prefixes, inward cores, outward rounding and the exact return-weight inequality.
At depth 33 the recurrence compares stopping in a destination core with extending
to four children; its values are integer numerators over powers of 57. It checks
the strict weighted gain with component weights 10000, 20000, 10000.

The accepted bound is log(57/50)/log(3), approximately 0.119267. It is a lower
bound, not the conjectured exact dimension. The paper explains how signed
nonlinear errors fit the one-step enclosure, why this persists after descendant
normalization, and how the weighted returns yield a Frostman measure.

## Integer sources and uniform tail

`alln20261020_parent_exact_logs.py` encloses logarithms with directed integer
rounding on a 2²⁵⁶ lattice and explicit series remainders. For every input row it
checks Cantor prefixes, strict corner signs and inclusion of the full derivative
ratio interval in an admissible slope band.

The fixed-scale verifiers check every closed parameter cell and strict inner
corner-image interval. Exact unions must cover the entire phase circle and all
parameter values in each prescribed interval. The two tail verifiers use
different logarithm expansions and interval-union implementations. The analytic
enclosure used by the tail is uniform for every scale beyond the stated cutoff;
checking finitely many large integer exponents would not suffice.

`alln20261020_assemble.py` verifies source hashes, report status and gap-free
integer range coverage. It assumes that the individual arithmetic verifiers
have been run. The `all` driver performs those runs first. The written geometric
transfer, admissible-band arguments, and cited Fermat theorem are external to
this computational assembly.

## Status and trust boundary

These are computer-assisted exact calculations in ordinary Python. They rely on
the Python implementation of integer/rational arithmetic, the verifier source,
and the mathematical argument connecting their outputs to the theorem. They are
not Lean kernel proofs, and no Lean files or verified Lean dependency graph are
present in this release. Input hashes establish identity, not mathematical truth.
