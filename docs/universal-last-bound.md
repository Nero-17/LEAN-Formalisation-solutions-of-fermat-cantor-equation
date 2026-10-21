# Uniform last-transition bound for every real exponent

Theorem 4.2 proves `lambda_max(n) < (sqrt(3)-1)/2` for every real `n>1`.
Section 4 and Appendix A provide the analytic reductions and exact predicates.
The complete package is included in **v1.2.0**. Its original archive bytes from
commit `dc581776594c83bd230ddba28eb701156b3c9c2b` are unchanged.

From the repository root, with Python 3.11 or later and its standard library:

```sh
python reproduce.py uniform-bound
```

The driver checks the archive and all 31 payload hashes, extracts to
`.reproduce/universal-last-bound/`, and runs all ten constituent exact checks.
The same replay is included in `python reproduce.py all`. For the dependency
and saved-report audit only, use `python reproduce.py uniform-bound-audit`.
Do not use `-O` or `-OO`. Full arithmetic replay can take substantial time.

The [unchanged standalone archive](../supplements/universal-last-bound/certificates.zip)
also works independently. To use the original standalone command from the
repository root:

```sh
python -m zipfile -e supplements/universal-last-bound/certificates.zip .reproduce-uniform-standalone
cd .reproduce-uniform-standalone
python verify_universal_bound.py --replay
```

Keep all 32 extracted files together. Without `--replay`, the original script
checks saved reports and dependency joins; it does not repeat the arithmetic.
The top-level driver adds archive and code/data identity checks.

| Part of the proof | Exact replay (within the extracted directory) |
| --- | --- |
| Near-one coefficient windows and small-denominator enumeration | `python parent_near_one_audit.py` |
| Exceptional n=7/6 | `python parent_cubic_cover_verify.py 0 7/6 n7_6_analytic_cover.jsonl` |
| Exceptional n=6/5 | `python parent_cubic_cover_verify.py 0 6/5 n6_5_analytic_cover.jsonl` |
| 6/5≤n≤2 | `python parent_continuous_cover_audit.py continuous_small_n_cover.jsonl` |
| 2≤n≤10 | `python parent_continuous_cover_audit.py continuous_medium_n_cover.jsonl` |
| 10≤n≤100 | `python parent_continuous_cover_audit.py continuous_high_n_cover.jsonl` |
| 100≤n≤250 | `python parent_continuous_cover_audit.py continuous_bridge_n_cover.jsonl` |
| 250≤n≤500 | `python parent_continuous_tight_audit.py continuous_upper_n_cover.jsonl` |
| All scales at least 1000 | `python parent_uniform_phase_audit.py adversarial_phase_small_M1000_D7.jsonl` |
| Remaining scales for n≥500 | `python parent_finite_shell_audit.py adversarial_finite_shells_N500.jsonl` |

The five continuous covers contain 89,240 records and 107,278 verified
subrectangles. The two tail groups contain 36 and 75 slabs, respectively.
These are complete closed parameter covers, not rational samples.

The endpoint λ=1/2 and the strict improvement below (sqrt(3)-1)/2 follow
analytically in the manuscript. No common gap in n or exact last-transition
value is claimed. This is a computer-assisted proof, not a Lean formalization.
