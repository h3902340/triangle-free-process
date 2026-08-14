# A combinatorial lower bound for $R(3,t)$

**Talk outline.** Deliver Bohman's triangle-free-process lower bound
\[
R(3,t)\;\ge\; c\,\frac{t^2}{\log t}
\]
without differential equations and without martingale concentration.

Full write-up: [`combinatorial-proof.tex`](combinatorial-proof.tex).

---

## 1. Goal (2 min)

- $R(3,t)$ = least $n$ such that every triangle-free $n$-vertex graph has an independent set of size $t$.
- Upper bound (Ajtai–Komlós–Szemerédi / Shearer): $R(3,t)=O(t^2/\log t)$.
- Lower bound (Kim; Bohman via the triangle-free process): $R(3,t)=\Omega(t^2/\log t)$.
- **Today:** a combinatorial proof of the lower bound, extracting the core of Bohman's argument.

Equivalently: build a triangle-free graph on $n$ vertices with
\[
\alpha(G)=O\bigl(\sqrt{n\log n}\bigr).
\]

---

## 2. What Bohman does (3 min)

The **triangle-free process**: start from the empty graph; repeatedly add a uniform random edge that does not create a triangle.

Bohman tracks, for each non-edge $\{u,v\}$:

| symbol | meaning | typical size after $i=t\,n^{3/2}$ steps |
|--------|---------|------------------------------------------|
| $Q$ | number of open pairs | $q(t)\,n^2$ |
| $X_{u,v}$ | open common neighbours | $x(t)\,n$ |
| $Y_{u,v}$ | partial vertices | $y(t)\sqrt{n}$ |

He derives the ODE system
\[
q'=-y,\qquad x'=-2xy/q,\qquad y'=-y^2/q+2x/q,
\]
with solution $q(t)=\tfrac12 e^{-4t^2}$, $x(t)=e^{-8t^2}$, $y(t)=4t\,e^{-4t^2}$, and concentrates the random variables around this trajectory by martingales.

**Consequence.** The process runs to $t=\Theta(\sqrt{\log n})$, produces $\Theta(n^{3/2}\sqrt{\log n})$ edges, and has $\alpha=O(\sqrt{n\log n})$.

We keep the combinatorial content (open pairs, density schedule $e^{-4t^2}$, hitting large sets) and discard the analytic machinery.

---

## 3. Combinatorial replacement (1 min)

| Bohman | These notes |
|--------|-------------|
| one random edge per step | one **nibble** of $\Theta(\gamma n^{3/2})$ open edges per round |
| differential equations | discrete product $\theta_{i+1}=\theta_i\,e^{-4\gamma}(1+O(\gamma^2))$ |
| Azuma–Hoeffding | averaging over $s$-subsets + triangle cleanup |
| dynamic concentration | induction on four invariants |

---

## 4. Construction (5 min)

**Parameters.** Small $\gamma\ll\delta\ll 1\ll C$, and
\[
T=\Bigl\lfloor\frac{\delta}{\gamma}\sqrt{\log n}\Bigr\rfloor,
\quad
m=\bigl\lfloor\tfrac12\gamma\,n^{3/2}\bigr\rfloor,
\quad
\alpha_*=C\sqrt{n\log n}.
\]

**Open pairs.** Given triangle-free $G$, a non-edge is *open* if adding it creates no triangle.

**One round**, from $G_i$ with open set $\mathcal{O}_i$, $|\mathcal{O}_i|=\theta_i\binom{n}{2}$:

1. **Nibble.** Consider all $m$-subsets $S\subseteq\mathcal{O}_i$.
2. **Clean.** Delete from $S$ every edge that lies in a triangle of $G_i\cup S$; call the result $S^\star$.
3. **Select.** Choose an $S$ that minimizes a potential $\Phi$ enforcing the invariants below.
   (Finite average $\Rightarrow$ a minimizer exists.)

Run $T$ rounds. Output $G=G_T$, which is triangle-free by construction.

---

## 5. Invariants (3 min)

Maintained by induction for $i\le T$:

1. **(I1)** $\theta_i=(1\pm i\gamma^2)\,e^{-4i\gamma}$.
2. **(I2)** all codegrees $\le(\log n)^2$.
3. **(I3)** all degrees $\le 2i\gamma\sqrt{n}$.
4. **(I4)** every $K$ of size $\alpha_*$ still independent in $G_i$ retains
   \[
   \bigl|\mathcal{O}(G_i)\cap\binom{K}{2}\bigr|
   \;\ge\;
   \tfrac12\,e^{-4i\gamma}\binom{\alpha_*}{2}.
   \]

**(I1) is the discrete $e^{-4t^2}$.**  
One-round averaging shows a typical open edge has $\sim 4\gamma\sqrt{n}$ partial vertices, so a nibble of $m$ edges closes a $4\gamma$-fraction of the open pairs:
\[
\theta_{i+1}=\theta_i\,e^{-4\gamma}(1+O(\gamma^2)).
\]
The product solves to $e^{-4i\gamma}$ by induction—**no ODE**.

---

## 6. Independence number by counting (5 min)

Fix $K$ with $|K|=\alpha_*$. While $K$ is independent, (I4) says it still holds many open pairs.

Fraction of nibbles that miss $K$ entirely:
\[
\Bigl(1-\frac{Q_K}{|\mathcal{O}_i|}\Bigr)^{m}
\;\le\;
\exp\Bigl(-\frac{m\,Q_K}{|\mathcal{O}_i|}\Bigr)
\;=\;
\exp\bigl(-\Omega(\gamma C^2\sqrt{n}\,\log n)\bigr).
\]

Over $T$ rounds, fraction of constructions that keep $K$ independent:
\[
\exp\bigl(-\Omega(C^2\delta\sqrt{n}\,(\log n)^{3/2})\bigr).
\]

Number of candidate sets $K$:
\[
\binom{n}{\alpha_*}\le\exp\bigl(O(C\sqrt{n}\,(\log n)^{3/2})\bigr).
\]

Average number of surviving bad sets $<1$ for $C\gg 1/\delta$.  
**Hence some construction has $\alpha(G)<\alpha_*$.**

---

## 7. Finish (1 min)

\[
\alpha(G)<C\sqrt{n\log n}
\quad\Longrightarrow\quad
R(3,t)>n=\Theta\Bigl(\frac{t^2}{\log t}\Bigr)
\quad\text{for }t=C\sqrt{n\log n}.
\]

---

## 8. Board summary

```
empty graph
    │  repeat T ~ √log n / γ times
    ▼
nibble m ~ γ n^{3/2} open edges
    │
    ▼
delete edges in new triangles          (cleanup)
    │
    ▼
θ ← θ · e^{-4γ}                        (discrete product)
    │
    ▼
every large K still has ~ e^{-4iγ} |K|² open pairs
    │
    ▼
those pairs get hit  ⇒  α < C √(n log n)
```

**Key identity (remember this):**
\[
\frac{(\\#\text{edges})}{n^2}\cdot\alpha_*^2
\sim
\frac{n^{3/2}\sqrt{\log n}}{n^2}\cdot n\log n
=
(\log n)^{3/2}\sqrt{n}/n^{0}
\quad\text{(enough to beat }\binom{n}{\alpha_*}\text{)}.
\]

---

## 9. What we do *not* claim

- The optimal constant $\tfrac14-o(1)$ of Bohman–Keevash / Fiz Pontiveros–Griffiths–Morris.
- A fully explicit (deterministic polynomial-time) construction; the best explicit bound remains Alon's $\Omega(t^{3/2})$.
- A martingale-free analysis of the *one-edge-at-a-time* process itself—we replaced it by a block nibble so that averaging suffices.

---

## References

- T. Bohman, *The triangle-free process*, Adv. Math. 221 (2009).
- J. H. Kim, *The Ramsey number $R(3,t)$ has order of magnitude $t^2/\log t$*, RSA 7 (1995).
- J. Shearer, *A note on the independence number of triangle-free graphs II*, JCTB 53 (1991).
