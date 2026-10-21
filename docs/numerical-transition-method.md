# Numerical squares in the phase diagram

These are **heuristic, finite-resolution estimates** of transition
parameters, not Hausdorff-dimension values and not certified bounds.
Blue squares estimate first transitions; red squares estimate last transitions.
The exact blue circles at n=2 and n=4, the pale blue irrational first-transition
line, and the shaded sufficient regions retain their analytic meaning. The red horizontal line at λ=1/3 records Theorem 3.1 for every real n>1;
no numerical irrational last-transition value is asserted.

## Last-transition calculation

Reflect the second coordinate by setting v=1-y. On each genuine Cantor
cylinder x=lambda^k X, v=lambda^m Y, with X,Y in
(1-lambda)+lambda C_lambda, compare the opposite corner values of

    (nk-m) log(lambda) + n log(X) - log(n) - log(Y)
      - log((1-(1-lambda^m Y)^n)/(n lambda^m Y)).

The residual increases with X and decreases with Y. Subdivide surviving
tail-coordinate squares into their four Cantor children. Work on the symmetric
half arc x<=y. Evaluate small differences using log1p and expm1.

The coarse scan used lambda=0.250,0.252,...,0.498, depth 20, and k=0,...,6.
The refined scan used lambda=0.2500,0.2505,...,0.3500, depth 22, and k=0,...,12.
Candidate low-growth parameters from the refined scan were rechecked in
descending order at 50 decimal digits and depth 34, with k=0,...,12. Cases
with surviving branches were then checked to depth 52; cases whose sampled
cylinders were already empty required no deeper subdivision. Candidate
m values were selected by intersection of the full cylinder intervals with
the actual curve, not by a fixed arbitrary list of m values.

For each local cylinder, regress the logarithm of the surviving-square count
over its last seven computed levels and divide by log(1/lambda). The final
check labels a parameter as low-growth only if **no tested cylinder** has both
a slope at least 0.025 and a final count at least 8. A slope above 0.08 with
at least 12 squares allows early numerical growth classification. The node
caps are 1200 in the double-precision scan and 256 in the high-precision check.
These cutoffs are computational conventions, not mathematical criteria for
dimension positivity. In particular, growth rates are not asserted to equal
Hausdorff dimension.

The plotted estimate is the midpoint of the final selected grid cell of
width 0.0005. The cell width is **not** an error bound: intervening narrow
gaps, isolated parameters, deep near-axis cylinders, and long transients can
be missed. A known zero-dimensional witness can also provide a lower anchor;
any such anchor is recorded explicitly in the CSV, never substituted silently.
For n=5, the exact certificates documented in `n5-numerical-anchor.md` give a witness near
0.2699992564030913, which lies above the last low-growth uniform-grid sample.

## First-transition calculation

The blue squares use a finite-cylinder survival onset proxy. The initial grid
starts at 0.2501 with step 0.0005 and k=0,...,12. At each parameter, candidate
cylinders are pruned at depth 18 in double precision. Survivors are rechecked
at 50 decimal digits, to depth 52 or a node cap of 512. The grid cell before
the first surviving sample is scanned with step 0.0001 and k=0,...,24.
The plotted value is the first surviving refined sample minus 0.00005,
clipped below at 1/4. This midpoint convention is not an error estimate.

Survival at finite depth does **not** establish positive Hausdorff dimension.
These squares are exploratory proxies for the onset, rather than validated
approximations to the true first transition. The grid is not an exhaustive
search of parameters or cylinders; narrow earlier windows and transient
survival can be missed or misclassified. Values close to 1/4 do not prove
that the first transition equals 1/4. The exact circles are retained from
the manuscript's proved results, not inferred from the computation.

## Validation and limitations

The local computation empties all tested cylinders at the known zero-dimensional
parameters n=2,lambda=0.26 and n=3,lambda=0.304, and observes growth at lambda=1/3.
The first attempted global finite-square count was rejected: the flat curve
near the axis produces spurious finite-scale growth even at known zero-dimensional
parameters. Local scaling removes this particular artefact but does not resolve
the infinite-scale question. Higher-precision checks also rejected several
shallow candidate locations; the coarse and refined positions are retained in
the CSV for comparison rather than presented as accurate digits.

The 25 rational exponents are exactly those displayed in the original figure:
2<=n<=8, reduced denominator at most 3. No interpolation between the squares is
intended. The finite grid cannot establish that a selected feature is the true
last transition.

## Reproduction

All scripts and raw traces are in `experiments/phase-transitions/` in this repository.
The figure scripts and the final CSV tables are in `figures/`. Install the
optional numerical dependencies with `python -m pip install -r requirements-figures.txt`.
See [the experiment README](../experiments/phase-transitions/README.md) for
the complete command sequence and for fresh versus cached runs.

The n=5 marker uses a rounded algebraic zero-dimensional anchor in addition to
the grid. Its exact root, finite certificates and infinite-tail argument are
documented in [n5-numerical-anchor.md](n5-numerical-anchor.md). The decimal in the
CSV is a plotting convention; neither it nor the plotted midpoint is a proved
last-transition value. The initial high-precision trace and global probes are
retained as rejected diagnostics, explicitly excluded from the final export.
