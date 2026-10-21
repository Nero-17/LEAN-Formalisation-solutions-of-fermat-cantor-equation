# All real exponents at λ=1/3

This is the certificate guide for Theorem 3.1 and Appendix A. For direct commands
below, first run `python reproduce.py prepare`, then change directory to
`.reproduce/`. The repository-level stage commands in the main README perform
the same checks without this directory change.

Generation programs have names including `scan`, `repair`, `phase`, `model`,
`sources`, `search` and `retry`. They retain the original search history and may
contain unsuccessful candidates. Their outputs require the independent checks
below; the executable driver selects the accepted branches. Search and discovery programs may require NumPy (`python -m pip install numpy`);
the exact verification stages use the standard library. Most generators
write relative to `work/` and should only run in a disposable workspace.

Accepted coverage and replay commands

1. Denominator b >= 110 (16 exact intervals):
   python work/thirdreal20261021_rational_verify.py

2. Reduced fractions 1 < a/b < 2187, 2 <= b <= 109:
   python work/thirdreal20261021_adversarial_scan.py 2187
   python work/thirdreal20261021_adversarial_repair.py 2187
   Inputs: rational_scan_2187.json and rational_repaired_2187.json, with
   the common thirdreal20261021_ prefix. The exact partition is
   8033550 = 7738063 + 294016 + 1464 + 7.

3. Continuous layers m=7,...,11 (650,508,470,552,547 cells):
   python work/thirdreal20261021_parent_layers.py 7 8 9 10 11
   Inputs: rational_grouped_fixed_m*.json with the same prefix. Each
   cell covers every denominator 2,...,109 at a single assigned endpoint
   for that denominator. Different endpoint rotations are not pooled.

4. Six axis-limit sources and their actual integer-scaled curves:
   python work/thirdreal20261021_adversarial_nearone.py
   python work/thirdreal20261021_adversarial_87.py
   python work/thirdreal20261021_adversarial_returns.py 3291854706059752449652/2493145389759550335983 15
   python work/thirdreal20261021_adversarial_general_source.py
   python work/thirdreal20261021_adversarial_532_verify.py
   The nearone.py command checks 24/23,19/18,13/12; _87.py checks 8/7;
   general_source.py checks 11/4; _532_verify.py checks 53/2. The separate returns.py
   command checks the full 8/7 return recurrence; see also the source input
   irrational_87_return_scan.json. Each check specifies its accepted
   complete record; unsuccessful candidate records are not conclusions.

5. Actual-curve source at 8/3 and independent return replay:
   python work/thirdreal20261021_parent_actual83_verify.py
   python work/thirdreal20261021_irrational_83_actual_verify.py
   python work/thirdreal20261021_rational_actual83_returns_verify.py
   python work/thirdreal20261021_rational_actual83_returns_compare.py
   The last command compares the independent interval histories and
   records the candidate hash. Return depth 17, margin 1/10000000.

6. Previously verified large-exponent sources, m=12,13,14 and m>=15:
   python work/thirdreal20261021_adversarial_large.py
   This command checks prior input hashes, legal cylinders and complete
   parameter joins; it does NOT rerun their logarithm calculations.
   Full prior verification programs and data are included under the
   alln20261020_ prefix. Their command-line arguments are documented in
   those programs and in the main README of this repository.

7. Logical partition and completed-receipt consistency:
   python work/thirdreal20261021_adversarial_final.py
   This adoption check does not replace the substantive checks above.

The mathematical proofs of the source transfer, irrational exponent case,
perfectness and strict-return dimension bound are in the manuscript.
`docs/source-manifest.json` records the uncompressed SHA-256 of every exact input and program.

