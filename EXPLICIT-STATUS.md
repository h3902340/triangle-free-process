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
- Energy at least `3/4` of `#T · W` puts a quarter of the energy on points of multiplicity `#T / 2`.
- The high-multiplicity core has size at most `4E/#T²`.
- Two `3/4`-dense subsets that miss a shift force `|U ∩ (U+σ)| ≤ |U|/2`.
- An affine image of a short interval of forbidden differences packs like `{1,…,d}`.
- An exact cylinder over an interval of `T`-steps has size at most `q/(d'+1)`.
- An exact cylinder over an arithmetic progression of `T`-steps packs the same way.
- A nonzero difference has at most one unsigned-parabola representation.
- Energy equals the sum of pairwise shifted-fibre intersections; off-diagonal energy is the remainder after neighbouring mass.
- Energy above \(W + B\cdot|T|\cdot(|T|-1)\) forces one off-diagonal intersection larger than \(B\).
- Two-thirds energy on mean size \(\ge q/3\) with fibres at most \(q/2\) forces \(|T|^2/9\) heavy ordered pairs and a star of degree \(|T|/9\) (Lean: `card_heavy_pair_set`, `exists_heavy_star`). Structure, not a size bound.
- If \(A\) misses \(B+\sigma\), then \(|A\cap(A+\sigma)|\le|A\setminus B|\). Neighbouring independence therefore bounds one self-translate by the fringe.
- Maximal energy makes every nonempty shifted fibre equal. Fibres of size \(\ge q/2\) cannot be strictly aligned; twice-random equality on those fibres is an exact cylinder.
- Two-thirds of maximal energy produces the same high-multiplicity core as three-quarters.
- Mean size \(\ge q/3\) and alignment force two-thirds energy, so the intermediate window is empty on every medium fibre. Medium aligned fibres have a high-multiplicity core (structure, not a size bound).
- On \(T=\{1,\dots,d\}\) with \(2d\le q\), every pair of \(T_x\)-fibres is \(T\)-adjacent. A heavy pair is therefore one almost-disjoint translate.
- The total off-diagonal fringe is \(|T|W-E\). A star with intersections above \(|A_s|(1-|A_s|/q)\) has self-translates at most random on average. That is a discrepancy, not a packing.
- A complete *affine* AP of uniformly below-random lags packs: `|U|(L+c+1) ≤ (c+1)q` (Lean: `pack_window`, including the window expansion). A `3/4`-close in-star along any common difference is such an AP (Lean: `pack_quarter_in_star_ap`). High-vertex out-neighbourhoods produce quadratic lags and do not pack this way. Average-only / `K=2` discrepancy and AP-poor neighbourhoods do not.

The SOTA independence-number bound for $A_q$ is **not** Lean-verified.

## Proved for Family A

- Triangle-free, degree $O(\sqrt{n\log n})$, constructible in $\mathrm{poly}(n)$.
- Open $G_2$-edges survive cleanup, so $\alpha(A_q)\le\alpha(H)$.
- Lift lemma: $\alpha(G_2)\le\ell\min(\alpha(G_R),\alpha(G_B))$.
- Structured seed independent sets (line, function graph, vertical / horizontal packing) have size $O(q\log q)$.
- After the $\mathrm{GL}_2$ sample, those structured sets do **not** lift to $G_2$-independent sets of SOTA size (`incidences.tex`).
- Tight 4-interval of medium fibres is impossible for $q>3$ (`energy-increment.tex`).
- Strict mixing: energy at most random and neighbouring mass $\ge q$ force an empty fibre (Lean: `strict_mixing_empty`).
- Medium aligned fibres ($|B_x|\ge q/3$) have a $1/2$-close star (`inverse-energy.tex`). This is structure, not a size bound, except for a `3/4`-close in-star whose high neighbours contain an AP of $T$-steps (Lean: `pack_quarter_in_star_ap`). A high-vertex $N^+$ is interval-dense on $T$-dense $x$, but those lags are quadratic. In-neighbours of $t=i+1$ are `{i+2,…,d}` (Lean: `intervalT_in_mem`). Half-intersection does not beat the random overlap when $|U|\le q/2`.
- Exact cylinders over a $T$-interval or any AP of $T$-steps pack by the interval lemma (Lean: `exact_cylinder_pack_ap`).
- Three-quarters of maximal energy produces a high-multiplicity core of size $O(\overline m)$ at any fibre size (Lean: `three_quarters_energy_core`, `high_multiplicity_core_card`).
- Half-intersection: two $3/4$-dense subsets that miss a shift force $|U\cap(U+\sigma)|\le|U|/2$ (Lean: `half_intersection`).
- Strictly-mixing $T$-dense fibres: $|A|=O(q\sqrt{\log q})$.
- Aligned AP-cylinders: $O(q\log q)$.
- Heavy closed stars contribute $O(\sqrt{n\log n})$ (`open-edges.tex`).
- Vertical-line and $x$-axis lifts have blue edges (`explicit_family.py --diagnose`).

## Not proved

1. **Intermediate-energy fibres** of size in $(q^{1/3}(\log q)^{-O(1)}, q/3)$. The window $[q/3,q/2]$ is empty of intermediate energy: alignment there is two-thirds energy (Lean: `aligned_implies_two_thirds`, `aligned_medium_has_core`), and size $q/2$ cannot be strictly aligned (Lean: `no_aligned_of_half_fibres`). Medium aligned fibres have a high-multiplicity core. On a $T$-dense $x$ some high-vertex $N^+$ and some in-star $N^-$ are interval-dense (Lean: `intervalT_out_mem`, `intervalT_in_mem`); high-vertex lags are quadratic and do not feed `pack_window`. A complete *affine* AP of uniformly below-random lags packs (Lean: `pack_window`); a `3/4`-close in-star along any common difference is such an AP (Lean: `pack_quarter_in_star_ap`). The leftover medium stars are average-only (`K=2`), high-vertex quadratic, or AP-poor (Weyl). Also leftover: thin two-thirds-energy stars that are not exact, and thin AP-poor two-clusters ($|T_i|=o(d)$). Exact cylinders (any AP support) pack by the interval lemma (Lean: `exact_cylinder_pack_ap`). Fibres $\le q^{1/3}/(\log q)^{O(1)}$ cannot prevent an Alon-beating bound after the lift.
2. **Medium-star incidences / light-star second moment.** An oversized $M_I$ reduces to high seed energy of $\pi_R(I)$ and does not open a third gap (`open-edges.tex`). Light stars are under control at the weaker target $|I|\ge C\sqrt{n}\,(\log n)^{5}$ with $t_3=(\log n)^{2}$. The SOTA scale still needs a second moment. The Sidon count $\sum D(u)^2=O(d|P|+|P|^2)$ is not $o(|I|^2)$ at $|I|\sim\Delta$.

Until both are written, Family A is not a new explicit Ramsey bound. The inverse-energy gap is no longer a Freiman loss $q^\delta$.

The *graph* is a deterministic polynomial-time function of \(n\) (`explicit_family.py --n`). See [`polytime-derandomization.tex`](polytime-derandomization.tex).

## Small-$q$ checks

Greedy $\alpha(G_R)$ is $2q$–$3q$ (a vertical packing). Tight 4-intervals: $0$. At $q=3,5,7$ the cleaned graph is triangle-free; greedy $\alpha(A_q)$ is still above the SOTA target because $d$ is tiny. The scaling is asymptotic.
