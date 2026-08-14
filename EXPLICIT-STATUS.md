# Explicit-family status

| Object | Bound | Status |
|--------|--------|--------|
| Family L (lex-first HHKP config) | SOTA $\tfrac12$ | **Theorem.** Exponential time. |
| Family A (algebraic two bites) | SOTA $\tfrac12$ | **Conjectural.** Poly-time. |
| Alon Dual-BCH | $\Omega(k^{3/2})$ | Theorem, poly-time. |

## Lean-verified (see [`lean/`](lean/README.md))

These statements compile in Lean 4.33 + mathlib with no `sorry`:

- Fibre constraint: a seed-independent set cannot contain both \((x,y)\) and \((x+t,y+t^2)\).
- Tight 4-interval: tightness forces \(B_x=B_x+6\); for \(q>3\) the fibre is empty or \(\mathbb{F}_q\).
- Two fibres larger than \(q/2\) cannot be at a \(T\)-difference.
- A \(\{\pm 1,\ldots,\pm d\}\)-difference-free subset of \(\mathbb{F}_q\) has size at most \(q/(d+1)\).
- The parabola is a Sidon set in odd characteristic.
- Lift: a red-independent product set projects to a seed-independent set and \(\lvert I\rvert\le \ell\cdot\lvert\pi_R(I)\rvert\).
- Every-open-edge graphs are triangle-free; $\alpha$ is antitone in the edge set.
- Strict mixing empties a fibre; neighbouring shifted fibres are disjoint after $2t(t-s)$.
- The popular core carries at least half the fibre energy.
- An affine image of a short interval of forbidden differences packs like `{1,…,d}`.
- A nonzero difference has at most one unsigned-parabola representation.

The SOTA independence-number bound for $A_q$ is **not** Lean-verified.

## Proved for Family A

- Triangle-free, degree $O(\sqrt{n\log n})$, constructible in $\mathrm{poly}(n)$.
- Open $G_2$-edges survive cleanup, so $\alpha(A_q)\le\alpha(H)$.
- Lift lemma: $\alpha(G_2)\le\ell\min(\alpha(G_R),\alpha(G_B))$.
- Structured seed independent sets (line, function graph, vertical / horizontal packing) have size $O(q\log q)$.
- After the $\mathrm{GL}_2$ sample, those structured sets do **not** lift to $G_2$-independent sets of SOTA size (`incidences.tex`).
- Tight 4-interval of medium fibres is impossible for $q>3$ (`energy-increment.tex`).
- Strict mixing: energy at most random and neighbouring mass $\ge q$ force an empty fibre (Lean: `strict_mixing_empty`).
- Medium aligned fibres ($|B_x|\ge q/3$) cluster around a common core of size $O(\log q)$ (`inverse-energy.tex`).
- Strictly-mixing $T$-dense fibres: $|A|=O(q\sqrt{\log q})$.
- Aligned AP-cylinders: $O(q\log q)$.
- Heavy closed stars contribute $O(\sqrt{n\log n})$ (`open-edges.tex`).
- Vertical-line and $x$-axis lifts have blue edges (`explicit_family.py --diagnose`).

## Not proved

1. **Intermediate-energy fibres** of size in $(q^{1/3}(\log q)^{-O(1)}, q/3)$. Medium fibres cluster; exact and near-maximal pieces pack by the interval lemma (no Weyl). Half-intersection is vacuous for thin cores. Fibres $\le q^{1/3}/(\log q)^{O(1)}$ cannot prevent an Alon-beating bound after the lift.
2. **Medium-star incidences / light-star second moment.** Light stars are under control at the weaker target $|I|\ge C\sqrt{n}\,(\log n)^{5}$ with $t_3=(\log n)^{2}$. The SOTA scale still needs a second moment.

Until both are written, Family A is not a new explicit Ramsey bound. The inverse-energy gap is no longer a Freiman loss $q^\delta$.

## Small-$q$ checks

Greedy $\alpha(G_R)$ is $2q$–$3q$ (a vertical packing). Tight 4-intervals: $0$. At $q=3,5,7$ the cleaned graph is triangle-free; greedy $\alpha(A_q)$ is still above the SOTA target because $d$ is tiny. The scaling is asymptotic.
