# Mapping to the paper

Numbers refer to the manuscript checked on 21 October 2026. The LaTeX labels
identify the statements even if later edits change the printed numbering.

| Statement | Label | Evidence |
| --- | --- | --- |
| Theorem 3.8: known strict-separation cases | `thm:known-separation` | Cubic/quartic exclusions in `quick`; the circle exclusion family below; analytic first-threshold results remain in the paper |
| Theorem 5.3: unit-circle zero intervals | `thm:circle-zero-intervals` | `r008_evidence_gap_family.py` and the all-scale argument in the paper |
| Lemma 5.11: five additional periodicity bands | `lem:good-slopes` | `r003_digits_graph_certificate.json`, checked by `r003_digits_verify.py` |
| Theorem 5.13: every integer n ≥ 2 at λ = 1/3 has positive dimension | `thm:integer-powers` | All reproduction stages, together with the analytic transfer and external theorems cited in the paper |
| Theorem 5.14: explicit circle dimension bounds | `thm:circle-quantitative` | `branching_r010_adaptive_B_57_50_theta2.json`, exact independent weighted-return verifier, and the written Frostman argument |

The remaining analytical proofs are not certified by this repository. In
particular, neither a successful Python run nor the repository name implies a
Lean formalisation of the whole manuscript.
