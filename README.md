# LEAN-Formalisation-solutions-of-fermat-cantor-equation

Computational companion to **Solutions of xⁿ + yⁿ = 1 in λ-Cantor sets**.

This release contains exact-arithmetic certificates, independent Python verifiers,
and reproducible calculation records for the computer-assisted parts of the paper.
**It does not contain Lean proofs. No claim of Lean kernel verification is made.**
The repository name is reserved for the wider formalisation project; its current
verification status is the Python certificate release described here.

The mathematical objects are

\[
C_\lambda=\{(1-\lambda)\sum_{j\ge1}\varepsilon_j\lambda^{j-1}:\varepsilon_j\in\{0,1\}\},
\qquad E_{n,\lambda}=\{(x,y)\in C_\lambda^2:x^n+y^n=1\}.
\]

## Reproduce

Requirements: **Python 3.11 or later**, with its standard library only. No pip
packages, Lean installation, network connection, or original author's filesystem
are required after cloning. Do **not** use `python -O`, which disables assertions.

```sh
git clone https://github.com/Nero-17/LEAN-Formalisation-solutions-of-fermat-cantor-equation.git
cd LEAN-Formalisation-solutions-of-fermat-cantor-equation
python reproduce.py quick
python reproduce.py all
```

`quick` reruns the polynomial exclusions for the unit circle, the cubic and
quartic exclusions, and all five certified digital graphs. It is not a substitute
for the full run. `all` additionally reconstructs the nine binary-return
certificates, checks the nonlinear source transfer and the weighted circle
certificate, verifies all 531,140 logarithmic sources for 301 ≤ n ≤ 531440,
checks six complete fixed-scale parameter covers and two verifications of the
infinite tail, and finally assembles the integer ranges.

The first run expands compressed data into `.reproduce/work/`. Large JSON inputs
are distributed as deterministic gzip files; their uncompressed SHA-256 hashes
are checked before use. Allow about 1 GB of working space and substantial extra
RAM for the largest interval reconstructions. The complete run can take tens of
minutes or longer, depending on hardware. The commands below allow separate stages:

```sh
python reproduce.py audit
python reproduce.py returns
python reproduce.py integer-sources
python reproduce.py phase-covers
python reproduce.py assembly
```

`audit` checks archived input hashes only. `assembly` checks range coverage and
report/input consistency; it **does not rerun the substantive verifiers**.
For a fresh independent reproduction use `all`, or run every preceding stage
before `assembly`. Use a new `--workspace PATH` to start a fresh reproduction.
The runner leaves all distributed certificates unchanged, writes regenerated
reports to the chosen workspace, and saves each command's log and exit status.

For one specific check:

```sh
python reproduce.py returns --only weighted-circle
python reproduce.py phase-covers --only independent-infinite-tail
```

## What is checked

| Paper result / proof input | Certificate family | Reproduction stage |
| --- | --- | --- |
| Unit-circle zero-dimensional intervals above the first threshold | Exact rational Bernstein inequalities | `quick` |
| Strict separation for n = 3 and n = 4 | Prefix partitions and rational residual signs | `quick` |
| Five additional admissible slope intervals | All 1024 words; exact feasibility and graph ranks | `quick` |
| Nine exceptional small integer exponents | Complete closed-interval binary-return recursions | `returns` |
| Quantitative dimension lower bound for E₂,₁/₃ | 232304 intervals; exact weighted antichain recurrence | `returns` |
| Strict logarithmic sources for 301 ≤ n ≤ 531440 | Directed integer logarithm enclosures | `integer-sources` |
| Fixed scales m = 12, 13, 14 | Six complete closed parameter covers | `phase-covers` |
| Every integer exponent n ≥ 3¹⁵ | Finite certificate for a uniform analytic tail bound | `phase-covers` |
| No missing integer in the assembled positive-dimension theorem | Range union and report/input hashes | `assembly` |

The proof transferring these checks to the original infinite Cantor intersection
is mathematical, and remains in the paper. In particular, the infinite exponent
tail is covered by a uniform analytic enclosure, not by sampling large integers.
The all-integer result here concerns **positive dimension at λ = 1/3**. It does
not prove strict separation for every integer exponent. The conjectured exact
dimension of E₂,₁/₃ also remains outside this release.

## Files and records

- `cantor-dust/work/`: selected original scripts, certificates and calculation
  outputs. Historical filenames are retained to keep dependencies traceable.
- `docs/source-manifest.json`: exact uncompressed hashes and storage locations.
- `docs/verification.md`: verification predicates and the distinction between
  arithmetic checks and mathematical implications.
- `docs/reproduction-results.json`: checks actually rerun for this release.
- `reproduce.py`: portable driver; all generated files stay in a separate workspace.

Historical baseline reports sometimes say that exponents above 300 were still
unresolved. Those statements describe the scope of the earlier calculation;
the later `alln20261020_all_integer_coverage.json` combines the completed ranges.
Success flags in archived reports are not a replacement for rerunning the checks.

No manuscript source, private correspondence, access credentials, or raw agent
conversation logs are included. A numbered release fixes the material used for
the paper; later research should not silently change that release.
