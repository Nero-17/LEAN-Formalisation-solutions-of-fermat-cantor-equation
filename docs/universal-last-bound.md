# Uniform last-transition bound for every real exponent

Theorem 4.2 in the revised manuscript proves
`lambda_max(n) < (sqrt(3)-1)/2` for every real `n>1`.
The analytic proof and exact predicates are in Section 4 and Appendix A.
This supplements the earlier v1.1.0 materials; it is not included in that tag.

Download [the complete certificate package](../supplements/universal-last-bound/certificates.zip)
and extract it into an empty working directory. All 32 files must remain together.
The [reproduction guide](../supplements/universal-last-bound/README.txt) describes
the scopes and separates arithmetic replay from receipt/hash validation.

```sh
python verify_universal_bound.py --replay
```

Python 3 with its standard library is sufficient. Do not use `-O` or `-OO`.
The command replays the near-one exact comparisons, both exceptional actual
curves, the five continuous real-exponent covers, and the all-scale tail and
four remaining finite scale shells. A full replay can take substantial time.
The existing top-level `reproduce.py all` predates this supplement; run the
command above separately for Theorem 4.2.

Without `--replay`, the driver validates saved reports, data hashes, integral
scales and cylinder words. This is not a full arithmetic replay. All constituent
exact checkers had completed before the original dependency chain was accepted.
The publication integration additionally reran the dependency validation and
near-one exact comparisons. It did not repeat all previously accepted checks.

The archive contains SHA-256 hashes for every supplied input and verifier.
Archive SHA-256: `6aa17e842c47547c2d3ead46680914262a29b3bb1dc442ee8b45ec3bba4c72d2`.

The certificates prove positivity for the entire contraction interval from
`(sqrt(3)-1)/2` to `1/2`; the endpoint at `1/2` is analytic. Strict persistence
at the lower boundary gives the manuscript's pointwise strict bound. No common
gap below the constant and no exact value of the last transition are claimed.
This is a computer-assisted proof, not a Lean formalization.
