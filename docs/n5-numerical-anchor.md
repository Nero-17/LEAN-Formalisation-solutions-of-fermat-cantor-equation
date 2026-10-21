# Exact algebraic anchor used by the n=5 numerical marker

Status: PROVED, computer-assisted with exact rational arithmetic.
This supplies the provenance of the n=5 anchor in the phase-diagram CSV. The decimal anchor is a rounded plotting value, not itself asserted to have exactly four points.

## The theorem

There is a specified algebraic number
\[
0.26999925640309133388080461073396780010<\lambda_*<
0.26999925640309133388080461073396780011
\]
such that the intersection of the Cantor dust with \(x^5+y^5=1\)
consists of exactly four points. Consequently
\[
\lambda_*\le\lambda_{\max}(5).
\]

Define
\[
\begin{aligned}
U(\lambda)&=(1-\lambda)(1+\lambda^2+\lambda^6)
              +\frac{\lambda^{12}}{1+\lambda},\\
V(\lambda)&=(1-\lambda)(1+\lambda+\lambda^7+\lambda^{10})
              +\frac{\lambda^{12}}{1+\lambda}.
\end{aligned}
\]
The parameter is the unique root in the stated interval of
\[
U(\lambda)^5+(1-\lambda^2V(\lambda))^5=1.
\]
The four points are the two axis points and
\((U(\lambda_*),1-\lambda_*^2V(\lambda_*))\), together with its exchange.

## Independent verification and all-scale argument

1. The prior all-shell certificate covers the entire parameter interval
   \([269999/10^6,270001/10^6]\). Every nonaxis point, after ordering its
   coordinates, belongs to the upper-branch core
   \(x=U,\ y=1-\lambda^2V\), where both auxiliary coordinates belong to
   \(1-\lambda+\lambda C_\lambda\). This includes all infinitely deep
   shells. An independent checker reconstructs the endpoint recursion.
2. For the periodic parameter, the checker constructs the integer
   polynomial obtained by multiplying the equation by \((1+\lambda)^5\).
   Horner evaluation has opposite strict signs at the decimal rational
   endpoints above. All fixed upper addresses have parameter derivative
   in \([-1,0]\); hence the defining residual is strictly decreasing.
3. Independent reverse-IFS endpoint evaluation, using a wider bracket
   than the original producer, verifies 54 strictly excluded rectangles.
   Their minimum margin exceeds \(1.9\cdot10^{-8}\). A complete four-child
   trie has exactly these leaves and the one retained word pair
   \(101000100000,110000010010\). No branch is omitted.
4. In the retained equal-depth cylinders, the derivative of the first
   tail as a function of the second lies strictly between
   \(0.1462157132262\) and \(0.1462158321275\). The actual periodic tails
   are both \(z=1/(1+\lambda_*)\).

For completeness the infinite-tail step is elementary. When a Cantor
point differs from \(z\), its first different digit determines the sign.
For a negative difference, its magnitude belongs to
\[
\frac{\lambda^{2j}}{1+\lambda}
[1-\lambda-\lambda^2,1],\qquad j\ge0;
\]
for a positive difference the same bound has \(\lambda^{2j+1}\).
Thus the ratio of two nonzero differences of the same sign belongs to
\[
\bigcup_{j\in\mathbb Z}\lambda^{2j}
[1-\lambda-\lambda^2,(1-\lambda-\lambda^2)^{-1}].
\]
It cannot lie in
\[
\left(\frac{\lambda^2}{1-\lambda-\lambda^2},
1-\lambda-\lambda^2\right).
\]
The independently checked curve derivative lies inside this gap, with
margins greater than 0.03527449 and 0.51088531. If there were a second
intersection in the retained cylinder, the increasing graph would force
same-sign tail differences. The mean value theorem would place their
ratio in the forbidden interval. Between the two alleged roots the
graph stays inside their coordinate rectangle, so the derivative bound
applies on the entire segment needed for that theorem.

The exact finite certificate is in
`fullseparation20261020_n5_joint_periodic_certificate.py/.json`.
The separate parent proof-check computations are in
`fullseparation20261020_n5_joint_parent_verify.py/.json`, and the
all-shell check in `fullseparation20261020_n5_parent_verify.py/.json`.

