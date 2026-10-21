Computational supplement: the uniform last-transition bound

Theorem: for every real n>1, lambda_max(n)<(sqrt(3)-1)/2.
The finite checks establish positive Hausdorff dimension for every
(sqrt(3)-1)/2 <= lambda < 1/2. The endpoint lambda=1/2 and the
pointwise strict improvement follow analytically in the manuscript.
No uniform gap below the constant is claimed.

Extract all files into one directory. Python 3 and the standard library
are sufficient. Do not use -O or -OO, which disable assertions.

Full independent arithmetic replay:
    python verify_universal_bound.py --replay

Saved-report, input-hash, structural and dependency validation only:
    python verify_universal_bound.py

The second command is not a substitute for the first. Each checker was
already run fully before the reports included here were accepted.
Full replay can take substantial time. Its log is universal_bound_replay.log.
The verification scripts import no floating-point search code and need
no third-party library. Search programs are deliberately not required.

The analytic two-band lemma, scale transfer, near-one grid argument,
continuous exponent reductions and finite-phase tail argument are in
the manuscript and summarized in UNIVERSAL_BOUND_PROOF.md. References
in that research summary to historical research reports are background;
the complete current mathematical reductions are in the manuscript.
This is a computer-assisted proof, not a Lean formalization.

Data groups:
- near-one exact rational-power checks and two actual-curve covers;
- five consecutive real-exponent rectangle covers from 6/5 to 500;
- all-scale logarithmic phase cover and four finite scale shells,
  covering every real n>=500.

MANIFEST.json gives the SHA-256 of all supplied code, data and reports.
The preserved original verification report states the non-strict bound;
the manuscript's strict bound additionally uses local persistence of
the strict actual source at the boundary contraction.

Unified repository entrypoint (v1.2.0):
    python reproduce.py uniform-bound
Run it from the repository root. It validates and extracts the unchanged ZIP
into .reproduce/universal-last-bound and executes the full replay.
The same stage is included in python reproduce.py all.
