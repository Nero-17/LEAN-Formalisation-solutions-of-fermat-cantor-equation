# Computational companion: solutions of the Fermat–Cantor equation

Experiments, algorithms, exact certificates and reproduction instructions for
**Solutions of xⁿ + yⁿ = 1 in λ-Cantor sets**. The manuscript uses **v1.1.0**.
The [paper-to-files index](docs/paper-index.md) identifies the material for each result.

The current release uses exact Python arithmetic. **It contains no Lean proofs
and makes no claim of Lean kernel verification.** The repository name also
serves the broader formalisation project.

## Contents

| Location | Contents |
| --- | --- |
| `cantor-dust/work/` | Exact certificates, generation/search algorithms, independent verifiers and historical receipts |
| `experiments/phase-transitions/` | First/last transition scans, raw traces, high-precision checks and CSV export |
| `figures/` | Published CSV tables, English/Chinese diagrams, plotting programs and Figure 1 TikZ sources |
| `docs/` | Paper index, verification predicates, exact file hashes and experiment methodology |
| `records/` | Commands, logs and results actually replayed during publication |

The full mathematical arguments remain in the paper. Finite-depth numerical
growth estimates are exploratory and are not used as proofs of positive dimension.
Failed or incomplete discovery candidates are retained where needed to reproduce
the search; only the specifically selected, independently checked records are certificates.

## Exact reproduction

Python **3.11 or later**, standard library only. Do not use `python -O`.

```sh
git clone https://github.com/Nero-17/LEAN-Formalisation-solutions-of-fermat-cantor-equation.git
cd LEAN-Formalisation-solutions-of-fermat-cantor-equation
git checkout v1.1.0
python reproduce.py audit
python reproduce.py quick
python reproduce.py real-quick
python reproduce.py all
```

`audit` verifies input hashes only; `quick` checks polynomial exclusions and
digital graphs; `real-quick` checks the denominator cover and two independent
sources at n=8/3. `all` additionally runs all integer-source, return, phase-cover
and all-real stages, then the n=5 numerical anchor. A full run can take tens of
minutes or longer and several GB of memory. Use a fresh `--workspace PATH` to
start an independent replay. Compressed JSON is expanded there and all outputs
stay separate from the distributed inputs.

Individual stages, in order:

```sh
python reproduce.py returns
python reproduce.py integer-sources
python reproduce.py phase-covers
python reproduce.py assembly
python reproduce.py real-quick
python reproduce.py real-sources
python reproduce.py real-phase-covers
python reproduce.py real-returns
python reproduce.py real-assembly
python reproduce.py numerical-anchor
```

`assembly` and `real-assembly` check coverage joins and receipts; on their own,
they do not rerun the substantive arithmetic. `all` runs those checks first.
For one job, use e.g. `python reproduce.py real-returns --only 8-over-3-returns`.
See [verification](docs/verification.md) and [all-real certificates](docs/real-exponents.md).

## Numerical experiments and figures

```sh
python -m pip install -r requirements-figures.txt
python reproduce_figures.py
```

This checks the archived experiment hashes, rebuilds both 25-row CSV tables,
compares them with the publication, and generates both phase diagrams in
`.reproduce-figures/figures/`. It uses the archived scan traces; it does not rerun
the expensive scans. The Chinese plot needs Microsoft YaHei or an appropriate
CJK font configured in its plotting script. `--tables-only` skips plotting.
The [experiment README](experiments/phase-transitions/README.md) gives the full
fresh-scan sequence. The [methodology](docs/numerical-transition-method.md)
explains finite-depth cutoffs, rejected diagnostics and limitations.

## Records and versioning

`docs/source-manifest.json` records the uncompressed SHA-256 of exact inputs;
`docs/experiments-manifest.json` covers numerical and figure inputs. Deterministic
gzip is only a storage format. Hash equality establishes identity, not truth.

The 29-job full integer/circle replay in `docs/reproduction-results.json` and
`records/2026-10-21/` belongs to v1.0.0. The new publication replay is recorded
separately in `docs/reproduction-results-v1.1.0.json`; it explicitly states which
new checks were rerun. Earlier all-real verification receipts accompany their
inputs. Neither archived success flags nor a packaging audit replace full replay.

The release includes the computer-assisted positive-dimension theorem for every
real n>1 at λ=1/3. It does not assert an exact dimension formula, a uniform
positive bound in n, or separation of the two transitions for every exponent.
