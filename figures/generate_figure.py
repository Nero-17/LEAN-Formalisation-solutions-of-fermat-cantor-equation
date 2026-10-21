"""Generate the TikZ source for the two exact level curves.

Grey squares are the third finite approximation, not plotted points of
the limiting intersection. Python's standard library suffices.
"""
from itertools import product
from math import cos, sin, pi, sqrt
from pathlib import Path

starts = [sum(d / 3**(i+1) for i, d in enumerate(word))
          for word in product((0, 2), repeat=3)]
out = [
    r"\begin{tikzpicture}[x=4.1cm,y=4.1cm,font=\small]",
]
for panel in (0, 1):
    out.append(r"\begin{scope}[shift={(" + str(panel * 1.55) + r",0)}]")
    for x in starts:
        for y in starts:
            out.append(
                rf"\fill[black!22] ({x:.9f},{y:.9f}) rectangle "
                rf"({x+1/27:.9f},{y+1/27:.9f});"
            )
    out.append(r"\draw[->] (-.03,0)--(1.07,0);")
    out.append(r"\draw[->] (0,-.03)--(0,1.07);")
    out.append(r"\node[below left] at (0,0) {$0$};")
    out.append(r"\node[below] at (1,0) {$1$};")
    out.append(r"\node[left] at (0,1) {$1$};")
    out.append(r"\begin{scope}\clip (0,0) rectangle (1,1);")
    if panel == 0:
        points = [(cos(pi*i/400), sin(pi*i/400)) for i in range(201)]
    else:
        points = []
        for i in range(401):
            a = i / 400
            remainder = 18621 - a*a - 12672*a
            b = 2*remainder/(10188 + sqrt(10188**2 + 36*remainder))
            points.append((a, b))
    out.append(r"\draw[red!75!black,line width=.85pt] plot coordinates {")
    out.extend(f"({x:.10f},{y:.10f})" for x, y in points)
    out.append("};")
    out.append(r"\end{scope}")
    if panel == 0:
        x, y = 566.5 / 3**7, 6336.5 / 3**8
        out.append(rf"\draw[blue!70!black] ({x:.8f},{y:.8f}) circle[radius=.035];")
        out.append(rf"\draw[blue!70!black,<-] ({x+.03:.8f},{y-.02:.8f})--(.48,.84);")
        out.append(r"\node[right,blue!70!black] at (.48,.84) {\scriptsize cylinder};")
        out.append(r"\node[right] at (1.07,0) {$x$};")
        out.append(r"\node[above] at (0,1.07) {$y$};")
    else:
        out.append(r"\node[right] at (1.07,0) {$a$};")
        out.append(r"\node[above] at (0,1.07) {$b$};")
    out.append(r"\end{scope}")
out.append(r"\end{tikzpicture}")
Path(__file__).with_name("cantor-circle.tex").write_text(
    "\n".join(out) + "\n", encoding="utf-8"
)
