# Computational coverage audit (v1.2.0)

This audit compares the English and Chinese manuscripts, including the new
uniform-bound sections introduced in manuscript commit `c6858e6`, with the subsequent Introduction
and Section 4 edits through `9dcfae3` preserved, with the
distributed certificates and executable reproduction commands. It audits
computational dependencies and replay; it is not a new proof of the analytic
reductions and is not a Lean formalization.

## Findings and repairs

The uniform last-transition certificates were already present in the ZIP added
at repository commit `dc58177`, with a standalone replay command and a local
index entry. They were absent from `reproduce.py all`. The README still told
readers to check out v1.1.0, which predates that supplement. Version v1.2.0
provides one pinned release and includes the supplement in the unified replay.

Both repository plotting scripts had changed without corresponding updates to
their input hashes or published plots. Consequently the figure reproduction
entrypoint rejected its inputs. The Chinese manuscript also retained the old
plot. Both languages, theorem references, plots and manifests are synchronized.

The supplement's standalone instructions assumed an extracted working directory.
The new root-level command validates the archive and every payload hash,
extracts into a separate workspace, and invokes the complete arithmetic replay.
The standalone extraction sequence remains documented.

## Every computational proof input

Run these commands from the repository root. Except for the figures, Python
3.11 or later with its standard library suffices. Use no optimization flag.
Individual stages share `.reproduce/`; choose a new `--workspace PATH` for a
fresh independent reproduction. The full command is `python reproduce.py all`.

| Paper item / computational input | Complete stage command | What is checked |
| --- | --- | --- |
| Lemma 2.9, digital admissibility graphs | `python reproduce.py quick --only digital-graphs` | All 1024 words and the five supplied rank/cycle graphs |
| Theorem 2.11, quantitative unit-circle lower bound | `python reproduce.py returns --only weighted-circle` | All 232304 partition intervals, exact weighted recursion, cores and source constants |
| Theorem 3.1, small integer sources and nine exceptional returns | `python reproduce.py returns` | Sources, nonlinear transfer, and complete return reconstructions for 9,10,23,25,28,31,32,78,82 |
| Theorem 3.1, integer sources 301 through 531440 | `python reproduce.py integer-sources` | Four batches of directed logarithmic and derivative-ratio inequalities |
| Theorem 3.1, continuous scales 12,13,14 and the unbounded tail | `python reproduce.py phase-covers` | Six closed parameter covers and two independent checks of the uniform tail |
| Theorem 3.1, integer coverage joins | `python reproduce.py assembly` | Range union and input/report consistency, after the preceding arithmetic stages |
| Theorem 3.1, reduced denominator at least 110 | `python reproduce.py real-quick --only rational-lattice-width` | The exact sixteen-source open cover |
| Theorem 3.1, 8033550 reduced rational exponents below 2187 | `python reproduce.py real-sources` | Complete classification, strict sources, 1464 repairs and the seven exceptional fractions |
| Theorem 3.1, continuous scales 7 through 11 | `python reproduce.py real-phase-covers` | Five closed covers, including every denominator 2 through 109 on every assigned cell |
| Theorem 3.1, actual source at 8/3 | `python reproduce.py real-quick` | Two independent actual-curve source checks |
| Theorem 3.1, seven exceptional rational exponents | `python reproduce.py real-returns` | Actual-source/error inequalities and complete binary returns, including the 17-level 8/3 reconstruction and history comparison |
| Theorem 3.1, all-real coverage joins | `python reproduce.py real-assembly` | Final partition, retained-tail joins and receipts, after all substantive stages |
| Theorem 4.2, near-one windows, two exceptional curves, five real-exponent covers and the infinite tail | `python reproduce.py uniform-bound` | All ten exact checks in the [expanded command table](universal-last-bound.md) |
| Theorem 4.5, polynomial zero-dimensional intervals | `python reproduce.py quick --only polynomial-gaps` | Rational Bernstein coefficient bounds for every polynomial exclusion |
| Additional cubic/quartic finite exclusions | `python reproduce.py quick` | Exact prefix coverage and signed residuals |
| Figure 2, algebraic n=5 zero-dimensional anchor | `python reproduce.py numerical-anchor` | Full-shell reduction and the retained periodic core; the infinite-tail argument is in [the anchor note](n5-numerical-anchor.md) |

Introduction Theorems 1.1 and 1.3 use the same computations as body
Theorems 3.1 and 4.2, respectively; the unit-circle consequence is also
proved quantitatively in Theorem 2.11. These need no separate certificates.

The analytic construction for irrational exponents, general dimension upper
bounds, the strict-return-to-Frostman arguments, endpoint persistence and the
case λ=1/2 remain mathematical arguments in the paper. They are not additional
finite calculations lacking certificates. Computations attributed to other
authors in the literature review are not asserted as results of this repository.

## Numerical experiments and figures

```sh
python -m pip install -r requirements-figures.txt
python reproduce_figures.py
```

This audits the 23 experiment/figure inputs, rebuilds both 25-row numerical
tables from raw archived traces, checks table equality, and renders both phase
diagrams. The [experiment guide](../experiments/phase-transitions/README.md)
also gives all commands for fresh scans. Finite-depth estimates are not proof
certificates or rigorous transition bounds. Figure 1 is an illustration with
its TikZ sources and generator included in `figures/`.

## Integrity, dependencies and replay evidence

The audit resolves all 32 explicit code/data filename mentions in the two
manuscripts and their included sections. The exact replay has 53 top-level
jobs; the uniform-bound job runs ten constituent checkers. Every entrypoint
exists. Its transitive import closure consists of 43 supplied Python modules
and standard-library dependencies. Discovery scripts may additionally require
NumPy; no search program or third-party package is needed for exact replay.

`python reproduce.py audit` checks 191 primary files, 31 supplement payload
files, and 23 experiment/figure files, with hashes pinned by the three manifests
in `docs/`. It does not prove the mathematics. The two assembly stages and
`uniform-bound-audit` are likewise not substitutes for substantive replay.

Completed execution evidence is recorded in
`docs/reproduction-results-v1.2.0.json` and `records/2026-10-21-v1.2.0/`.
The record distinguishes full arithmetic replay, saved-report joins, input
identity checks, and numerical export/plotting. Earlier v1.0.0 and v1.1.0
records are retained as historical records and are not relabelled as new runs.
