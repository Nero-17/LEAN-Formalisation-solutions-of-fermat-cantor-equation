# Computational companion: solutions of the Fermat–Cantor equation

Experiments, algorithms, exact certificates and reproduction instructions for
**Solutions of $x^\alpha + y^\alpha = 1$ in $\lambda$-Cantor sets**. The current manuscript keeps the rational-exponent part of Theorem 3.1 as a
computer-assisted proof. Start with the [PDF certificate reader\'s guide](docs/certificate-guide.pdf)
([LaTeX source](docs/certificate-guide/main.tex)); it contains the detailed
construction, numerical tables and verification predicates moved out of the paper.
The guide uses the unchanged **v1.2.0** certificate data and programs.
The current proofs of Lemma 2.9, Theorem 2.11 and Theorem 4.2 are analytic;
the older [uniform-bound certificates](docs/universal-last-bound.md) remain historical material.
The [paper-to-files index](docs/paper-index.md) identifies the material for each result.

The manuscript now denotes the real exponent by $\alpha$. In the verification
programs, data fields and archived records, `n` denotes this same exponent.
The current plotting scripts use $\alpha$; the fixed v1.2.0 figures retain the
earlier label $n$. The numerical data and certificates are unchanged.

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

The paper presents the analytic arguments and the construction ideas for the
rational case; the PDF guide supplies the detailed computational reduction. Finite-depth numerical
growth estimates are exploratory and are not used as proofs of positive dimension.
Failed or incomplete discovery candidates are retained where needed to reproduce
the search; only the specifically selected, independently checked records are certificates.

## Exact reproduction

Python **3.11 or later**, standard library only. Do not use `python -O`.

```sh
git clone https://github.com/Nero-17/LEAN-Formalisation-solutions-of-fermat-cantor-equation.git
cd LEAN-Formalisation-solutions-of-fermat-cantor-equation
git checkout v1.2.0
python reproduce.py audit
python reproduce.py quick
python reproduce.py real-quick
python reproduce.py all
```

`audit` verifies input hashes only; `quick` checks polynomial exclusions and
digital graphs; `real-quick` checks the denominator cover and two independent
sources at n=8/3. `all` additionally runs all integer-source, return, phase-cover
and all-real stages, the n=5 numerical anchor, and the full uniform
last-transition replay (ten constituent exact checks). A full run can take tens of
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
python reproduce.py uniform-bound
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

Use `python reproduce.py all --list` to inspect every expanded command.
`python reproduce.py uniform-bound-audit` checks saved reports only.
The current coverage audit is [documented here](docs/computational-coverage.md).

## Records and versioning

`docs/source-manifest.json` records the uncompressed SHA-256 of exact inputs;
`docs/experiments-manifest.json` covers numerical and figure inputs. Deterministic
gzip is only a storage format. `docs/supplement-manifest.json` additionally
pins the uniform-bound archive, whose internal manifest covers all 31 payload
files. `audit` checks all three groups. Hash equality establishes identity, not truth.

The 29-job full integer/circle replay in `docs/reproduction-results.json` and
`records/2026-10-21/` belongs to v1.0.0. The selected v1.1.0 publication replay is recorded
separately in `docs/reproduction-results-v1.1.0.json`. The v1.2.0 full audit
is recorded in `docs/reproduction-results-v1.2.0.json` and
`records/2026-10-21-v1.2.0/`, including the new uniform-bound replay. Earlier all-real verification receipts accompany their
inputs. Neither archived success flags nor a packaging audit replace full replay.

The historical v1.2.0 release includes certificates for positive dimension at
λ=1/3 and for the former proof of Theorem 4.2. In the current manuscript only
the rational-exponent part of Theorem 3.1 requires the computational companion. It does not assert an exact dimension formula, a uniform
positive bound in n, or separation of the two transitions for every exponent.

