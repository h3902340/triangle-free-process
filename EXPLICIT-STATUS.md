# Explicit-family status

| Object | Bound | Status |
|--------|--------|--------|
| Family L (lex-first HHKP config) | SOTA $\tfrac12$ | **Theorem.** Exponential time. |
| Family A (algebraic two bites) | SOTA $\tfrac12$ | **Conjectural.** Poly-time. |
| Alon Dual-BCH | $\Omega(k^{3/2})$ | Theorem, poly-time. |

## Proved for Family A

- Triangle-free, degree $O(\sqrt{n\log n})$, constructible in $\mathrm{poly}(n)$.
- Open $G_2$-edges survive cleanup, so $\alpha(A_q)\le\alpha(H)$.
- Lift lemma: $\alpha(G_2)\le\ell\min(\alpha(G_R),\alpha(G_B))$.
- Structured seed independent sets (line, function graph, vertical / horizontal packing) have size $O(q\log q)$.
- After the $\mathrm{GL}_2$ sample, those structured sets do **not** lift to $G_2$-independent sets of SOTA size (`incidences.tex`).
- Tight 4-interval of medium fibres is impossible for $q>3$ (`energy-increment.tex`).
- Strictly-mixing $T$-dense fibres: $|A|=O(q\sqrt{\log q})$.
- Aligned AP-cylinders: $O(q\log q)$.
- Heavy closed stars contribute $O(\sqrt{n\log n})$ (`open-edges.tex`).
- Vertical-line and $x$-axis lifts have blue edges (`explicit_family.py --diagnose`).

## Not proved

1. **Inverse energy for non-AP fibres.** Converts “energy above random” into “fibres are almost a common translate of the parabola”. Standard BSG+Freiman; quantitative loss $q^\delta$ with $\delta<1/3$ would already beat Alon after the lift.
2. **Medium-star incidences / light-star second moment.** Needed to finish the open-edge lemma at the SOTA scale $C\sqrt{n\log n}$.

Until both are written, Family A is not a new explicit Ramsey bound.

## Small-$q$ checks

Greedy $\alpha(G_R)$ is $2q$–$3q$ (a vertical packing). Tight 4-intervals: $0$. At $q=3,5,7$ the cleaned graph is triangle-free; greedy $\alpha(A_q)$ is still above the SOTA target because $d$ is tiny. The scaling is asymptotic.
