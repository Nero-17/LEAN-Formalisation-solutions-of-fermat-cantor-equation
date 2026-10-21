# Paper-to-files index (v1.1.0 with the uniform-bound supplement)

Theorem numbers refer to the English and Chinese manuscripts at this release.
The logical proof and reductions are in the manuscript; this index locates the
finite calculations and the exploratory figure data.

| Manuscript item | Files / command |
| --- | --- |
| Figure 1: Cantor squares and level curves | `figures/cantor-circle.tex`, `cantor-circle-zh.tex`, `generate_figure.py` |
| Figure 2: Hausdorff phase transition diagram | `figures/generate_phase_diagram.py`, `_zh.py`, both CSV tables; `python reproduce_figures.py` |
| Figure 2 numerical squares | Raw traces and scan/export algorithms in `experiments/phase-transitions/`; [methodology](numerical-transition-method.md) |
| Digital graph admissibility used in the source arguments | `r003_digits_verify.py`, `r003_digits_affine_parameter_returns.py`; `quick` |
| Theorem 2.11: quantitative circle lower bound | `branching_r010_adaptive_B_57_50_theta2.json`, `r010_parent_weighted_return_verify.py`; `returns --only weighted-circle` |
| Theorem 3.1: positive dimension for all real n>1 | [All-real guide](real-exponents.md), `thirdreal20261021_*`; `real-quick`, `real-sources`, `real-phase-covers`, `real-returns`, `real-assembly`, together with the retained integer stages |
| Theorem 4.5: uniform strict last-transition bound for every real n>1 | [Uniform-bound guide](universal-last-bound.md); `supplements/universal-last-bound/certificates.zip`; extract and run `python verify_universal_bound.py --replay` |
| Integer subcase of Theorem 3.1 | `r003_*`, `alln20261020_*`; `returns`, `integer-sources`, `phase-covers`, `assembly` |
| Unit-circle polynomial gap exclusions | `r008_evidence_gap_family.py`; `quick --only polynomial-gaps` |
| Supporting cubic and quartic finite exclusions | `continuity20261020_low_n3_certificate.py`, `separation20261020_parent_check.py`; `quick` |
| Exact n=5 zero-dimensional anchor used in Figure 2 | `fullseparation20261020_n5_*`; `numerical-anchor`; [anchor argument](n5-numerical-anchor.md) |

Except for explicitly named directories, exact filenames in the table live in
`cantor-dust/work/`; large JSON is stored with an extra `.gz` suffix and expanded
by the driver. Generation algorithms and dependencies are supplied alongside
the accepted certificates. Exact files keep historical names for traceability.

Analytic results (including the irrational-exponent construction, general
dimension upper bounds, and the reductions from strict returns to a Frostman
bound) need no numerical certificate. They remain in the paper.
