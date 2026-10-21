# Phase-transition experiments

These files underlie the numerical squares of Figure 2, not rigorous estimates
of Hausdorff dimension. Read [the methodology](../../docs/numerical-transition-method.md).

## Cached reproduction

From the repository root:

```sh
python -m pip install -r requirements-figures.txt
python reproduce_figures.py
```

This audits input hashes, copies inputs to a disposable workspace, reconstructs
the two final CSV tables and plots them. Both tables must match the published
25 rows. Archived traces are used; full parameter scans are not rerun.

## Fresh scans

Use a separate directory with `experiments/phase-transitions/` and `figures/`
subdirectories. Copy the four `.py` files here into the former and the figure
scripts into the latter. Do not copy the JSONL traces: the programs resume by
skipping completed exponents. Then run, from that separate root:

```sh
python experiments/phase-transitions/scan_last_transition.py --grid
python experiments/phase-transitions/scan_last_transition.py --refine
python experiments/phase-transitions/check_transition_precision.py
python experiments/phase-transitions/check_transition_precision.py --deep
python experiments/phase-transitions/export_transition_estimates.py
python experiments/phase-transitions/estimate_first_transition.py
python figures/generate_phase_diagram.py
python figures/generate_phase_diagram_zh.py
```

Scans may take hours. The default arrays use double precision; candidate checks
use 50-decimal-digit mpmath arithmetic. Finite depth, selected axis scales, node
caps and a finite parameter grid all limit the conclusions. A grid midpoint is
not a rigorous bound on a transition.

## Data provenance

`last-transition-grid.jsonl` and `-refined.jsonl` contain the broad scans;
`-precision.jsonl` and `-deep.jsonl` contain the accepted precision checks.
`first-transition-scan.jsonl` records the onset proxy. The final export also
retains the documented n=5 algebraic zero-dimensional anchor; its rounded
decimal is not an exact parameter certificate.

`last-transition-precision-initial.jsonl` and the probe `.txt` files preserve
superseded diagnostics. They are excluded from the final CSV export. In
particular, the global-square growth proxy was rejected because of spurious
near-axis growth. Input hashes and packaging-only path changes are recorded
in `docs/experiments-manifest.json` at the repository root.
