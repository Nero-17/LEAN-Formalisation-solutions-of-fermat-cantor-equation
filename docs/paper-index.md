# Paper-to-files index

The [Lean formalisation index](../formalisation/THEOREMS.md) covers all 34
numbered English environments at frozen Overleaf commit `429d53b`, with exact
formal statements and compilation evidence. The computational index below
describes the separately versioned Python companion.

Current manuscript status, 24 October 2026. Numerical inputs and programs are
unchanged from their documented releases. The current paper has no certificate
appendix: its detailed rational-exponent construction and former Appendix A are
in the [PDF reader's guide](certificate-guide.pdf)
([LaTeX source](certificate-guide/main.tex)).

| Current manuscript item | Status and supporting files |
| --- | --- |
| Lemma 2.9: admissible slope bands | Analytic proof in the paper; older digital graph checks are historical support. |
| Theorem 2.11: positive dimension for the unit circle | Analytic proof in the paper; the older weighted-circle certificate proves a separate stronger quantitative bound. |
| Theorem 3.1: positive dimension at λ=1/3 | Irrational exponents: analytic. Rational exponents: [PDF guide](certificate-guide.pdf), [replay commands](real-exponents.md), retained integer stages and `thirdreal20261021_*`. The case α=2 is analytic. |
| Theorem 4.2: strict uniform last-transition bound | Analytic proof in the current paper. [Former certificates](universal-last-bound.md) are retained for historical reproducibility. |
| Theorems 4.3–4.6: circle onset, gap intervals and separation | Analytic proofs in the paper. `r008_evidence_gap_family.py` provides an optional arithmetic cross-check, not an omitted proof step. |
| Theorem 4.8: almost-everywhere dimension | Analytic proof in the paper. |
| Figure 1 | `figures/cantor-circle.tex`, `cantor-circle-zh.tex`, `generate_figure.py`. |
| Figure 2 | `figures/generate_phase_diagram.py`, `_zh.py`, both CSV tables; `python reproduce_figures.py`. Numerical estimates remain exploratory; [methodology](numerical-transition-method.md). |
| Exact n=5 numerical anchor for Figure 2 | `fullseparation20261020_n5_*`; `numerical-anchor`; [anchor argument](n5-numerical-anchor.md). |

Exact files with historical names live in `cantor-dust/work/` unless otherwise
specified. Large JSON inputs use a `.gz` suffix and are expanded by the driver.
Generation programs and unsuccessful candidates are not accepted certificates.

For Theorem 3.1 run the integer stages `returns`, `integer-sources`,
`phase-covers`, `assembly`, followed by `real-quick`, `real-sources`,
`real-phase-covers`, `real-returns`, `real-assembly`. The `returns` suite also
contains the historical weighted-circle calculation. Neither assembly checks nor
hash audits replace the substantive arithmetic checks. The broader `all` suite
also replays historical material, including the old Theorem 4.2 certificates.

