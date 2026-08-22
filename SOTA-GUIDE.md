# Lecture notes: is [arXiv:2510.19718](https://arxiv.org/pdf/2510.19718) the state of the art?

**Paper.** Zion Hefty, Paul Horn, Dylan King, Florian Pfender,
*Improving \(R(3,k)\) in just two bites*, [arXiv:2510.19718](https://arxiv.org/abs/2510.19718) (2025).

**These notes.** Written for a master’s student who has seen calculus and discrete math, but not Ramsey theory. Every word that has a technical meaning is defined before it is used. Theorems are labelled. Proofs are written as a list of claims you can check.

All logarithms are natural logs (base \(e\)), as in the paper.

---

## 0. Short answer

**Yes, for the lower bound.** As of August 2026, this paper has the best proved *lower* bound

\[
R(3,k)\;\ge\;\Bigl(\tfrac12+o(1)\Bigr)\frac{k^2}{\log k}.
\]

It improved the previous best lower bound \(R(3,k)\ge(\tfrac13+o(1))k^2/\log k\) of Campos–Jenssen–Michelen–Sahasrabudhe (May 2025).

**No, it does not determine \(R(3,k)\).** The best *upper* bound is still Shearer (1983):

\[
R(3,k)\;\le\;(1+o(1))\frac{k^2}{\log k}.
\]

So the current sandwich is a factor of \(2\):

\[
\Bigl(\tfrac12+o(1)\Bigr)\frac{k^2}{\log k}
\;\le\;
R(3,k)
\;\le\;
(1+o(1))\frac{k^2}{\log k}.
\]

The paper (and CJMS) *conjecture* that the truth is the lower bound. That conjecture is an **upper-bound** problem. This paper does not prove it.

The symbol \(o(1)\) means “a quantity that goes to \(0\) as \(k\to\infty\).” So “\(\tfrac12+o(1)\)” means: the ratio \(R(3,k)\cdot(\log k)/k^2\) has liminf at least \(\tfrac12\).

---

## 1. Notation I will use without apology

| Symbol | Meaning |
|---|---|
| \(\mathbb{N}\) | positive integers \(1,2,3,\dots\) |
| \([n]\) | the set \(\{1,2,\dots,n\}\) |
| \(\binom{n}{k}\) | number of \(k\)-element subsets of an \(n\)-set; \(0\) if \(k>n\) |
| \(\lvert A\rvert\) | number of elements of a finite set \(A\) |
| \(A\subset B\) | \(A\) is a subset of \(B\) (maybe equal) |
| \(\exp(x)\) | \(e^x\) |
| \(\log x\) | natural logarithm |
| \(o(1)\) | \(\to 0\) as the large parameter \(\to\infty\) |
| \(O(f)\) | at most \(C\lvert f\rvert\) for some constant \(C\) and all large inputs |
| \(\Omega(f)\) | at least \(c\lvert f\rvert\) for some constant \(c>0\) and all large inputs |
| whp | “with high probability”: probability \(1-o(1)\) |

**Lemma 1.1 (two binomial bounds).**
For integers \(n\ge k\ge 1\),

\[
\Bigl(\frac{n}{k}\Bigr)^k
\;\le\;
\binom{n}{k}
\;\le\;
\Bigl(\frac{en}{k}\Bigr)^k.
\]

**Proof.**
\(\binom{n}{k}=\frac{n(n-1)\cdots(n-k+1)}{k!}\).
The numerator is at least \((n-k+1)^k\) and at most \(n^k\). Also \(k!\ge(k/e)^k\) by the standard integral bound \(\log k!\ge\int_1^k\log x\,dx=k\log k-k+1\), which rearranges to \(k!\ge(k/e)^k\cdot e\). The cruder \(k!\ge(k/e)^k\) is enough for the upper bound: \(\binom{n}{k}\le n^k/k!\le(en/k)^k\). The lower bound \(\binom{n}{k}\ge(n/k)^k\) is \(\frac{n}{k}\cdot\frac{n-1}{k}\cdots\frac{n-k+1}{k}\ge 1\) after pairing, or more simply each of the \(k\) factors in the falling factorial is at least \(n-k+1\ge n/k\) when \(k\le n/2\); for \(k>n/2\) the inequality is easy by \(\binom{n}{k}=\binom{n}{n-k}\). We will only use the upper bound.

**Lemma 1.2 (\(1-x\le e^{-x}\)).**
For every real \(x\), \(1+x\le e^x\). In particular, for \(0\le p\le 1\), \(1-p\le e^{-p}\).

**Proof.**
The tangent line to \(e^x\) at \(0\) is \(1+x\), and \(e^x\) is convex.

---

## 2. Graphs, from zero

### 2.1 The objects

**Definition 2.1 (graph).**
A **graph** \(G\) is a pair \((V,E)\) where \(V\) is a finite set of **vertices** and \(E\) is a set of unordered pairs of distinct vertices, called **edges**. We write \(V(G)=V\) and \(E(G)=E\). We do **not** allow loops (an edge from a vertex to itself) or multiple edges, unless we say so.

**Definition 2.2 (adjacent, degree).**
Two vertices are **adjacent**, or **neighbours**, if \(\{u,v\}\in E(G)\). The **neighbourhood** \(N(v)\) is the set of neighbours of \(v\). The **degree** \(\deg(v)=\lvert N(v)\rvert\). The **maximum degree** is \(\Delta(G)=\max_v\deg(v)\). The **average degree** is \(2\lvert E(G)\rvert/\lvert V(G)\rvert\).

**Definition 2.3 (triangle, clique).**
A **triangle** is three vertices \(a,b,c\) such that all three pairs \(ab,bc,ca\) are edges. A **clique** of size \(\ell\) (written \(K_\ell\)) is a set of \(\ell\) vertices in which every pair is an edge. A triangle is \(K_3\).

**Definition 2.4 (independent set, independence number).**
An **independent set** is a set of vertices that contains **no** edge. The **independence number** \(\alpha(G)\) is the size of a largest independent set.

**Example 2.5.**
The cycle on five vertices \(C_5\) (vertices \(1,2,3,4,5\), edges \(12,23,34,45,51\)) has no triangle, and \(\alpha(C_5)=2\) (you cannot pick three vertices with no two consecutive).

**Definition 2.6 (triangle-free).**
\(G\) is **triangle-free** if it contains no triangle.

### 2.2 The one-line fact that runs the whole subject

**Theorem 2.7 (neighbourhoods are independent).**
If \(G\) is triangle-free, then for every vertex \(v\) the set \(N(v)\) is independent. In particular

\[
\alpha(G)\;\ge\;\Delta(G).
\]

**Proof.**
Suppose two neighbours \(x,y\in N(v)\) were adjacent. Then \(\{v,x,y\}\) would be a triangle. So \(N(v)\) has no edges: it is independent, of size \(\deg(v)\). Taking a vertex of maximum degree gives \(\alpha(G)\ge\Delta(G)\).

**What this means.**
In a triangle-free graph you cannot make degrees large without automatically creating a large independent set. Any construction that wants *small* \(\alpha\) must also keep degrees from being much larger than \(\alpha\).

### 2.3 The random graph (only as a probability space)

**Definition 2.8 (\(G(n,p)\)).**
Fix \(n\in\mathbb{N}\) and \(p\in[0,1]\). The **Erdős–Rényi random graph** \(G(n,p)\) is the probability space of all graphs on a fixed vertex set of size \(n\), in which each of the \(\binom{n}{2}\) possible edges is included independently with probability \(p\).

Expected degree of a vertex is \(p(n-1)\approx pn\). We will not need deeper random-graph theory. We *will* need two tail inequalities, stated in §6.

---

## 3. Problem statement

### 3.1 The Ramsey number

**Definition 3.1 (the number \(R(3,k)\)).**
For an integer \(k\ge 2\), the **off-diagonal Ramsey number** \(R(3,k)\) is the smallest integer \(N\) such that **every** graph on \(N\) vertices contains either

- a triangle, or
- an independent set of size \(k\).

Equivalently, in the language of edge-colourings: \(R(3,k)\) is the smallest \(N\) such that every red/blue colouring of the edges of the complete graph \(K_N\) contains a red triangle or a blue clique of size \(k\). (Let the red edges be the edges of \(G\). A red triangle is a triangle in \(G\). A blue \(k\)-clique is an independent set of size \(k\) in \(G\).)

**Tiny exact values** (only for orientation; the paper is about large \(k\)):

| \(k\) | \(R(3,k)\) |
|---|---|
| \(3\) | \(6\) |
| \(4\) | \(9\) |
| \(5\) | \(14\) |

**Why \(R(3,3)=6\), as a complete argument.**

- *Upper bound \(R(3,3)\le 6\).* Take any graph \(G\) on \(6\) vertices and a vertex \(v\). Then \(\deg(v)\ge 3\) or the complement degree is at least \(3\). If \(\deg(v)\ge 3\), either two neighbours of \(v\) are adjacent (a triangle) or they are not (an independent set of size \(3\), together with the same argument in the complement if we started from non-neighbours). This is the usual classroom proof.
- *Lower bound \(R(3,3)>5\).* The \(5\)-cycle is triangle-free and has \(\alpha=2\). So there exists a \(5\)-vertex graph with no triangle and no independent set of size \(3\).

Exact values become hopeless quickly. The paper studies the **asymptotics**: the shape of \(R(3,k)\) as \(k\to\infty\).

### 3.2 What a lower bound *is*

To prove \(R(3,k)\) is *large*, you must show that there exist large graphs that avoid both structures. One example is enough.

**Theorem 3.2 (the dictionary).**
For integers \(n,k\ge 2\) the following are equivalent.

1. There exists a triangle-free graph on \(n\) vertices with \(\alpha(G)<k\).
2. \(R(3,k)>n\).

**Proof.**
\((1)\Rightarrow(2)\). The graph in (1) is an \(n\)-vertex graph with no triangle and no independent \(k\)-set. So the statement “every \(N\)-vertex graph has a triangle or an independent \(k\)-set” fails at \(N=n\). The smallest such \(N\) is therefore at least \(n+1\), i.e. \(R(3,k)>n\).

\((2)\Rightarrow(1)\). If \(R(3,k)>n\), then it is not true that every \(n\)-vertex graph has a triangle or an independent \(k\)-set. So some \(n\)-vertex graph has neither: it is triangle-free and \(\alpha<k\).

**The whole SOTA paper is a proof of (1) for**

\[
k=(1+\varepsilon)\sqrt{n\log n},
\]

with \(\varepsilon>0\) arbitrary and \(n\) large. Section 4 turns that into the formula with \(\tfrac12\).

### 3.3 The theorems of the paper, in the paper’s numbering

**Theorem A (HHKP, Theorem 1.3 — the graph statement).**
For every \(\varepsilon>0\) there exists \(n_0=n_0(\varepsilon)\) such that for all \(n\ge n_0\) there exists a triangle-free graph \(G\) on \(n\) vertices with

\[
\alpha(G)\;<\;(1+\varepsilon)\sqrt{n\log n}.
\]

**Theorem B (HHKP, Theorem 1.2 — the Ramsey statement).**

\[
R(3,k)\;\ge\;\Bigl(\tfrac12+o(1)\Bigr)\frac{k^2}{\log k}.
\]

Theorem B is a corollary of Theorem A plus algebra. We prove that corollary first, because it has no graph theory in it.

---

## 4. Why the constant is \(\tfrac12\)

**Theorem 4.1 (algebraic translation).**
Suppose that for every \(\varepsilon>0\) and all sufficiently large \(n\) there exists a triangle-free \(n\)-vertex graph with \(\alpha(G)<(1+\varepsilon)\sqrt{n\log n}\). Then Theorem B holds.

**Proof.**
Fix \(\varepsilon>0\). For large \(n\), Theorem 3.2 and the hypothesis give

\[
R\bigl(3,\,(1+\varepsilon)\sqrt{n\log n}\bigr)\;>\;n.
\]

Set \(k=(1+\varepsilon)\sqrt{n\log n}\). Then \(k^2=(1+\varepsilon)^2\,n\log n\), so

\[
n=\frac{k^2}{(1+\varepsilon)^2\log n}.
\]

We replace \(\log n\) by \(2\log k\). From the definition of \(k\),

\[
\log k=\log(1+\varepsilon)+\tfrac12\log n+\tfrac12\log\log n,
\]

hence \(\log n=(2+o(1))\log k\) as \(k\to\infty\). Therefore

\[
n=\frac{k^2}{(1+\varepsilon)^2\cdot(2+o(1))\log k}
=\frac{1}{2(1+\varepsilon)^2+o(1)}\cdot\frac{k^2}{\log k}.
\]

Since \(\varepsilon>0\) was arbitrary, we may take the constant in front of \(k^2/\log k\) to be any number strictly less than \(\tfrac12\). That is the meaning of \(\tfrac12+o(1)\) on the lower-bound side.

**Where the \(2\) comes from.**
\(k\) is about \(\sqrt{n\log n}\), so \(n\) is about \(k^2/\log n\). But \(n\) is also about \(k^2\), so \(\log n\) is about \(2\log k\). That factor \(2\) is the \(\tfrac12\).

---

## 5. One page of history (so you know what “SOTA” improved)

| Year | Bound | Who / method |
|---|---|---|
| 1930 | \(R(\ell,k)\) exists and is finite | Ramsey |
| 1980–83 | \(R(3,k)=O(k^2/\log k)\), constant \(1\) | Ajtai–Komlós–Szemerédi; Shearer |
| 1995 | \(R(3,k)\ge c\,k^2/\log k\), \(c\approx 1/160\) | Kim (nibble) |
| 2013 | constant \(\tfrac14\) | Bohman–Keevash; Fiz Pontiveros–Griffiths–Morris (triangle-free process) |
| May 2025 | constant \(\tfrac13\) | Campos–Jenssen–Michelen–Sahasrabudhe |
| Oct 2025 | constant \(\tfrac12\) | **HHKP, this paper** |

The **triangle-free process** starts from no edges and repeatedly adds a uniformly random edge that does not create a triangle. Analysing it is long (differential equations + martingales).

HHKP do something else: two sparse random graphs, overlaid at random, then a deterministic cleanup. No nibble, no differential equation.

---

## 6. Probability toolkit (four facts)

You do not need a probability course. You need these four statements.

**Theorem 6.1 (union bound).**
For any events \(A_1,\dots,A_M\),

\[
\mathbb{P}\bigl(A_1\cup\cdots\cup A_M\bigr)
\;\le\;
\sum_{i=1}^M\mathbb{P}(A_i).
\]

**Proof.**
The probability of a union is at most the sum of the measures. If the sum is \(o(1)\), then the probability that *any* of the events happens is \(o(1)\).

**Theorem 6.2 (Chernoff / Hoeffding, as the paper uses it).**
Let \(X_1,\dots,X_m\) be independent random variables with values in \(\{0,1\}\), and let \(S=\sum X_i\), \(\mu=\mathbb{E}S\). Then for every \(t\ge 0\),

\[
\mathbb{P}(S\ge\mu+t)\;\le\;\exp\Bigl(-\frac{t^2}{2(\mu+t/3)}\Bigr),
\]

and for \(0\le t\le\mu\),

\[
\mathbb{P}(S\le\mu-t)\;\le\;\exp\Bigl(-\frac{t^2}{2(\mu-t/3)}\Bigr).
\]

If \(t\ge\tfrac32\mu\), the upper tail simplifies to \(\mathbb{P}(S\ge\mu+t)\le\exp(-t/2)\).

**What this says in English.**
A sum of independent coin flips is very close to its mean. The probability of a deviation of size \(t\) is exponentially small in \(t^2/\mu\).

**Theorem 6.3 (McDiarmid’s bounded-differences inequality).**
Let \(W_1,\dots,W_m\) be independent random variables, and let \(Z=Z(W_1,\dots,W_m)\) be a real function. Suppose that changing the \(i\)-th input, while keeping the others fixed, changes \(Z\) by at most \(c_i\). Then for every \(t>0\),

\[
\mathbb{P}\bigl(Z\ge\mathbb{E}Z+t\bigr)
\;\le\;
\exp\Bigl(-\frac{t^2}{2\sum_i c_i^2}\Bigr),
\]

and likewise for the lower tail.

**What this says in English.**
If a quantity depends on many independent choices, and no single choice can swing it by much, then the quantity concentrates around its mean.

**Lemma 6.4 (first-moment deletion).**
If a nonnegative integer-valued random variable \(X\) has \(\mathbb{E}X<1\), then \(\mathbb{P}(X=0)>0\). In particular, if \(X\) counts “bad objects” and \(\mathbb{E}X=o(1)\), then whp there are no bad objects.

**Proof.**
\(\mathbb{E}X=\sum_{m\ge 0}m\,\mathbb{P}(X=m)\ge\mathbb{P}(X\ge 1)\). So \(\mathbb{P}(X\ge 1)\le\mathbb{E}X\). If \(\mathbb{E}X<1\) then \(\mathbb{P}(X=0)>0\).

This is the only “probabilistic method” philosophy you need: **if the expected number of bad \(k\)-sets is \(o(1)\), then some outcome has none.**

---

## 7. The construction, with every parameter defined

Fix \(\varepsilon\in(0,1/100)\) and a large integer \(n\). The paper also fixes two smaller error budgets \(0<\varepsilon_2\ll\varepsilon_1\ll\varepsilon\). All \(o(1)\) are as \(n\to\infty\).

### 7.1 Parameters

| Symbol | Value | Role |
|---|---|---|
| \(s\) | \(\log^2 n\) | blow-up / typical fibre size |
| \(m\) | \(n/s=n/\log^2 n\) | number of red names, and of blue names |
| \(\beta\) | \(\tfrac12\) | density constant that produces SOTA \(\tfrac12\) |
| \(p\) | \(\beta\sqrt{\log n\,/\,n}\) | edge probability in each seed |
| \(\kappa\) | \(1+\varepsilon\) | a little larger than \(1\), so the algebra has room |
| \(k\) | \(\kappa\sqrt{n\log n}\) | the independent-set size we want to forbid |

Floors and ceilings are ignored (they do not change any \(o(1)\)).

### 7.2 Two seed graphs (“two bites”)

Let \(V_R=\{r_1,\dots,r_m\}\) and \(V_B=\{b_1,\dots,b_m\}\) be disjoint.

- \(G_R\) is a random graph \(G(m,p)\) on \(V_R\) (the **red seed**).
- \(G_B\) is an independent copy of \(G(m,p)\) on \(V_B\) (the **blue seed**).

These are *not* the final graph. They are small.

### 7.3 Random labels

Let \(V=\{v_1,\dots,v_n\}\) be the final vertex set.

Choose an injection

\[
\pi:V\hookrightarrow V_R\times V_B
\]

uniformly at random among all injective maps. Write \(\pi(v)=(\pi_R(v),\,\pi_B(v))\). Each final vertex has a **red name** and a **blue name**, and no two final vertices share the same pair of names.

**Definition 7.1 (fibre).**
For \(r\in V_R\), the **red fibre** is \(F(r)=\pi_R^{-1}(r)\), the set of final vertices with red name \(r\). Blue fibres are defined the same way. Typically \(\lvert F(r)\rvert\approx s=\log^2 n\).

### 7.4 Product edges, before cleanup

**Definition 7.2 (red and blue product edges).**
Put a **red edge** between distinct \(u,v\in V\) when \(\pi_R(u)\pi_R(v)\) is an edge of \(G_R\).
Put a **blue edge** when \(\pi_B(u)\pi_B(v)\) is an edge of \(G_B\).

A pair may receive both colours. The paper keeps both and works with a multigraph. The independence number does not care about multiplicity.

**Definition 7.3 (product neighbourhood of a name).**
For \(r_i\in V_R\) write \(N(r_i)\) for its neighbourhood in the *seed* \(G_R\), and

\[
N_{r_i}\;=\;\bigcup_{r_j\in N(r_i)} F(r_j).
\]

This is the set of final vertices whose red name is a \(G_R\)-neighbour of \(r_i\). The **forward** neighbourhood \(N_{r_i}^+\) keeps only neighbours \(r_j\) with \(j>i\). That extra order is used when cleanup deletes the *last* edge of a monochromatic triangle.

### 7.5 The idea, in one paragraph

Each seed is sparse enough that a random graph of that density is below the triangle-deletion threshold on \(m\) vertices. Blowing a seed up by a factor \(s\) would give a triangle-free \(n\)-vertex graph with huge independent sets (a whole blown-up vertex). Overlaying *two* blow-ups at random, using the two names, makes each colour destroy the leftover independent sets of the other. New triangles appear, but they come in large bunches that share an edge, so deleting one edge kills many triangles. That is cheaper than ordinary “delete one edge from each triangle,” and it is why the construction can keep density \(p\sim\sqrt{\log n\,/\,n}\), above the classical deletion threshold \(1/\sqrt{n}\).

---

## 8. Cleanup: the output is triangle-free

This step is deterministic. No coin is flipped.

Order all pairs in \(V_R\) lexicographically (first by the smaller index, then the larger). Do the same for \(V_B\).

**Construction 8.1 (cleanup).**
Start from the red and blue product edges. Then:

1. **Three red edges.** In every red triangle, look at the three red name-pairs of its three edges. Delete the red product-edge whose red name-pair comes *last* in the lex order.
2. **Three blue edges.** The same, using blue names.
3. **Two red, one blue.** Delete the blue edge.
4. **Two blue, one red.** Delete the red edge.

Write \(G\) for the graph that remains.

**Theorem 8.2 (triangle-free).**
\(G\) is triangle-free.

**Proof.**
A triangle in the product uses some combination of red and blue edges.

- Three red: rule 1 deleted one of them.
- Three blue: rule 2 deleted one of them.
- Two red and one blue: rule 3 deleted the blue edge.
- Two blue and one red: rule 4 deleted the red edge.
- Three edges that are both colours: then in particular there is a red triangle and a blue triangle on the same three vertices, already destroyed by rules 1–2.

Those are all the colour patterns.

**Why this is cheap (heuristic, not needed for correctness).**
A typical seed-vertex is the red name of about \(s=\log^2 n\) final vertices. Many product-triangles therefore share the “last” edge in the lex order. Deleting that one edge removes a bunch of triangles at once. The factor \(s\) is the gain over spending one deletion per triangle.

---

## 9. Typical configurations

**Definition 9.1 (the event \(\mathcal{D}\)).**
Let \(C=100\). The configuration \((G_R,G_B,\pi)\) is **typical** (event \(\mathcal{D}\)) if all of the following hold for every pair of distinct names \(v,w\in V_R\cup V_B\):

1. fibres have size \(\bigl\lvert\lvert F(v)\rvert-\log^2 n\bigr\rvert\le\varepsilon_2\log^2 n\);
2. seed degrees satisfy \(\bigl\lvert\lvert N(v)\rvert-pm\bigr\rvert\le\varepsilon_2 pm\);
3. seed codegrees: if \(v,w\) have the same colour then \(\lvert N(v)\cap N(w)\rvert\le C\log n\);
4. product degrees satisfy \(\bigl\lvert\lvert N_v\rvert-pn\bigr\rvert\le\varepsilon_2 pn\);
5. product codegrees satisfy \(\lvert N_v\cap N_w\rvert\le C\log^3 n\);
6. projected codegrees across colours are at most \(2C\log^3 n\).

**Theorem 9.2 (most configurations are typical).**
\(\mathbb{P}(\mathcal{D})=1-o(1)\).

**Proof sketch, at the level you need.**
Each bullet is a count for a *fixed* vertex or pair: a fibre size, a degree, or a codegree. Each is a sum of independent (or hypergeometric) indicators whose mean is the displayed target. Theorem 6.2 says each single constraint fails with probability \(n^{-\Omega(1)}\) (in fact much smaller). There are \(O(m^2)=O(n^2/\log^4 n)\) vertices and pairs. The union bound (Theorem 6.1) leaves failure probability \(o(1)\).

The injection \(\pi\) is not an independent sample of \(n\) points, but an injective sample. That only *helps* concentration (sampling without replacement is more concentrated than with replacement). The paper treats this as routine; so will we.

On \(\mathcal{D}\), the final average degree after cleanup is still \((1+o(1))\sqrt{n\log n}\). We will not need the precise edge count, only that degrees are \(O(\sqrt{n\log n})\), which follows from (4) and the fact that cleanup only *deletes* edges.

---

## 10. Open pairs, closed pairs, and four buckets

To prove \(\alpha(G)<k\) we must show that a typical \(k\)-set \(I\subset V\) is **not** independent in the cleaned graph.

Fix \(I\subset V\) with \(\lvert I\rvert=k\).

**Definition 10.1 (star of a name).**
For a name \(v\in V_R\cup V_B\),

\[
X_v(I)\;=\;I\cap N_v.
\]

This is the set of vertices of \(I\) that are product-neighbours of the fibre of \(v\). The pairs among \(X_v(I)\) are the pairs of \(I\) that \(v\) **closes**: they already have a common neighbour, so adding an edge between them would complete a triangle.

**Definition 10.2 (closed and open pairs).**

\[
C(I)\;=\;\bigcup_{v\in V_R\cup V_B}\binom{X_v(I)}{2},
\qquad
O(I)\;=\;\binom{\pi(I)}{2}\setminus C(I).
\]

A pair inside \(I\) is **closed** if some name already witnesses a common neighbour. It is **open** otherwise.

Cleanup can delete edges, but it cannot *add* edges. So:

- a closed pair may or may not remain an edge;
- an **open** pair, if it is present as a red or blue product-edge, survives cleanup as an edge inside \(I\) (made precise in Theorem 11.1). Therefore, for \(I\) to be independent, **every remaining open pair must be a non-edge of the seeds**.

That is the engine: count open pairs, then charge \((1-p)^{\#\text{open}}\) for the event that they are all missing.

**Definition 10.3 (four buckets).**
Split names by the size of \(X_v(I)\):

| Bucket | Size of \(X_v(I)\) | Cutoff |
|---|---|---|
| \(H_I\) (heavy) | \(>t_1\) | \(t_1=\sqrt{n\log n}/\log\log n\) |
| \(L_I\) (large) | \(t_2<\lvert X_v\rvert\le t_1\) | \(t_2=n^{1/4+\varepsilon}\) |
| \(M_I\) (medium) | \(t_3<\lvert X_v\rvert\le t_2\) | \(t_3=n^{2\varepsilon}\) |
| \(S_I\) (small / light) | \(\le t_3\) | |

The number of pairs a name \(v\) closes is \(\binom{\lvert X_v(I)\rvert}{2}\). The plan:

- \(L_I\), \(M_I\), \(S_I\) together close only \(o(k^2)\) pairs;
- the only serious contribution is \(H_I\), and that contribution is controlled by the sizes of the two **projections** \(\ell_R=\lvert\pi_R(I)\rvert\) and \(\ell_B=\lvert\pi_B(I)\rvert\).

---

## 11. The bucket theorems

Throughout this section we work on the typicality event \(\mathcal{D}\), except where a probability over the seeds is stated.

### 11.1 Large stars: a deterministic double count

**Theorem 11.1 (large stars; HHKP Lemma 3.2).**
On \(\mathcal{D}\), for every \(k\)-set \(I\),

\[
\sum_{v\in L_I}\binom{\lvert X_v(I)\rvert}{2}\;=\;o(k^2).
\]

**Proof.**
*Step 1: \(L_I\) is not big.*
Take any \(L\subseteq L_I\). Inclusion-exclusion and the product-codegree bound \(\lvert X_u\cap X_v\rvert\le C\log^3 n\) from \(\mathcal{D}\) give

\begin{align*}
k=\lvert I\rvert
&\;\ge\;
\Bigl\lvert\bigcup_{v\in L}X_v(I)\Bigr\rvert
\;\ge\;
\sum_{v\in L}\lvert X_v\rvert
-\sum_{\{u,v\}\subset L}\lvert X_u\cap X_v\rvert\\
&\;\ge\;
\lvert L\rvert\cdot n^{1/4+\varepsilon}
-\binom{\lvert L\rvert}{2}C\log^3 n.
\end{align*}

If \(\lvert L\rvert=\lfloor n^{(1-\varepsilon)/4}\rfloor\), the first term is \(n^{(1-\varepsilon)/4}\cdot n^{1/4+\varepsilon}=n^{1/2+\varepsilon/2}\), which is \(\gg k\sim\sqrt{n\log n}\), while the second term is \(O\bigl(n^{(1-\varepsilon)/2}\log^3 n\bigr)=o(n^{1/2+\varepsilon/2})\). Contradiction. Hence \(\lvert L_I\rvert<n^{(1-\varepsilon)/4}\).

*Step 2: the stars are almost disjoint.*
The same count with this bound on \(\lvert L_I\rvert\) shows the intersection-correction is \(o(k)\), so

\[
\sum_{v\in L_I}\lvert X_v(I)\rvert\;\le\;(1+o(1))k.
\]

*Step 3: multiply by the maximum star size.*
Each star has size at most \(t_1=o(k)\), so

\[
\sum_{v\in L_I}\binom{\lvert X_v\rvert}{2}
\;\le\;
\frac{t_1}{2}\sum_{v\in L_I}\lvert X_v\rvert
\;=\;
o(k)\cdot k
\;=\;
o(k^2).
\]

No extra randomness was used.

### 11.2 Medium stars: an unusually dense bipartite graph

**Theorem 11.2 (medium stars; HHKP Lemma 3.3).**
With probability \(1-o(1)\), every \(k\)-set \(I\) satisfies \(\sum_{v\in M_I}\binom{\lvert X_v(I)\rvert}{2}=o(k^2)\).

**Proof.**
Write \(Y_I=\sum_{v\in M_I}\lvert X_v(I)\rvert\). If we show \(Y_I\le k\,n^{1/4-\varepsilon}\) for every \(I\), we are done: each medium star has size at most \(t_2=n^{1/4+\varepsilon}\), so

\[
\sum_{v\in M_I}\binom{\lvert X_v\rvert}{2}
\;\le\;
Y_I\cdot t_2
\;\le\;
k\,n^{1/2}
\;=\;
o(k^2),
\]

because \(k^2\sim n\log n\).

Suppose some \(I\) has \(Y_I>k\,n^{1/4-\varepsilon}\). Let \(B\subseteq M_I\) be a minimal subset with the same lower bound on its mass. Then \(\lvert B\rvert\le n^{-2\varepsilon}Y_I\le 2k\,n^{1/4-3\varepsilon}\), because each medium star has size \(>t_3=n^{2\varepsilon}\).

The mass \(Y_I\) counts incidences between names in \(B\) and vertices of \(I\). On \(\mathcal{D}\), each seed-edge lifts to \(O(\log^2 n)\) such incidences. So the bipartite graphs

\[
\bigl(B\cap V_R,\;\pi_R(I)\bigr)\quad\text{in }G_R,
\qquad
\bigl(B\cap V_B,\;\pi_B(I)\bigr)\quad\text{in }G_B
\]

together have \(\Omega\bigl(k n^{1/4-\varepsilon}/\log^2 n\bigr)\) edges.

For a *fixed* pair \((B,I)\) of those sizes, the number of seed-edges in those two bipartite graphs is a binomial random variable \(Z\sim\mathrm{Bin}(O(\lvert B\rvert k),p)\) with mean

\[
\mathbb{E}Z=O\bigl(k\cdot k n^{1/4-3\varepsilon}\cdot p\bigr)
=O\bigl(k^2 n^{1/4-3\varepsilon}\sqrt{\log n\,/\,n}\bigr)
=o\bigl(k n^{1/4-\varepsilon}/\log^2 n\bigr).
\]

So the event “this pair is that dense” is an upper tail with \(t\ge\tfrac32\mathbb{E}Z\). Theorem 6.2 gives probability at most \(\exp(-n^{3/4-2\varepsilon})\).

The number of candidate pairs is

\[
\binom{n}{k}\binom{2m}{O(kn^{1/4-3\varepsilon})}
\;\le\;
\exp\bigl(k\log n+O(kn^{1/4-3\varepsilon}\log n)\bigr)
\;=\;
\exp\bigl(o(n^{3/4-2\varepsilon})\bigr).
\]

Union bound: \(\exp(o(N))\cdot\exp(-N)=o(1)\) with \(N=n^{3/4-2\varepsilon}\). So whp no such overfull pair exists, and every \(Y_I\) is small.

### 11.3 Light stars: expectation plus bounded differences

**Theorem 11.3 (light stars; HHKP Lemma 3.4).**
With probability \(1-o(1)\), every \(k\)-set \(I\) satisfies \(\sum_{v\in S_I}\binom{\lvert X_v(I)\rvert}{2}=o(k^2)\).

**Proof.**
Split \(S_I\) into names that lie in the projections \(\pi_R(I)\cup\pi_B(I)\) and names that do not.

*Inside the projections.*
There are at most \(2k\) such names, and each light star has size \(\le n^{2\varepsilon}\), so they close at most \(2k\cdot n^{4\varepsilon}\) pairs. Since \(k\sim\sqrt{n\log n}\), this is \(o(k^2)\).

*Outside the projections.*
Write \(Z\) for the number of pairs of \(I\) closed by at least one outside light name. For a pair of \(I\) that does not already sit in a common fibre, the probability that some outside name closes it is at most

\[
2\bigl(1-(1-p^2)^m\bigr)\;\le\;2p^2 m\;=\;\frac{2\beta^2}{\log n}\;=\;\frac{1}{2\log n}
\]

when \(\beta=\tfrac12\). (A common neighbour in the red seed occurs with probability about \(p^2 m\), and likewise in blue.) So

\[
\mathbb{E}Z\;\le\;\frac{1}{2\log n}\binom{k}{2}+O(k\log^2 n)\;=\;o(k^2).
\]

To upgrade “expectation is small” to “every \(I\) at once,” apply Theorem 6.3. The inputs are the neighbourhoods of outside names. Editing one name changes \(Z\) by at most \(\binom{n^{2\varepsilon}}{2}\le n^{4\varepsilon}/2\). There are at most \(2m\) such names. Taking deviation \(t=k^2/\sqrt{\log n}\) gives

\[
\mathbb{P}(Z\ge\mathbb{E}Z+t)
\;\le\;
\exp\bigl(-\Omega(n^{1-8\varepsilon}\log^3 n)\bigr)
\;=\;
o\Bigl(\binom{n}{k}^{-1}\Bigr),
\]

because \(\log\binom{n}{k}=O(k\log n)=O(\sqrt{n}\,(\log n)^{3/2})\). Union bound over the \(\binom{n}{k}\) choices of \(I\): the failure probability is \(o(1)\).

**Why a first-moment bound is not enough at this scale.**
A crude estimate \(\sum\binom{d}{2}\le t_3\cdot k\cdot\Delta\) with \(\Delta\sim\sqrt{n\log n}\) and \(t_3=n^{2\varepsilon}\) is \(k^2\cdot n^{2\varepsilon}\), which is **not** \(o(k^2)\). The paper’s saving is this second-moment / bounded-differences argument over the random seeds. That is also why a deterministic polynomial-time copy of the construction does not automatically inherit the SOTA bound.

### 11.4 Heavy stars: convexity

**Theorem 11.4 (heavy stars; HHKP Lemma 3.5, qualitative form).**
On \(\mathcal{D}\), for every \(k\)-set \(I\), writing \(\ell_R=\lvert\pi_R(I)\rvert\) and \(\ell_B=\lvert\pi_B(I)\rvert\),

\[
\sum_{v\in H_I\cap V_R}\binom{\lvert\pi_B(X_v(I))\rvert}{2}
\;\le\;
(1+o(1))\min\Bigl\{\binom{k-\ell_R}{2},\;
\binom{pn}{2}+\binom{k-\ell_R-pn}{2}\Bigr\},
\]

and symmetrically with colours swapped. Also, same-colour projected heavy stars contribute only \(o(k^2)\) pairs.

**Proof.**
The same double count as in Theorem 11.1, now with threshold \(t_1=\sqrt{n\log n}/\log\log n\), shows \(\lvert H_I\rvert=O(\log\log n)\) and the heavy stars are almost disjoint. Seed degrees are \(O(pm)=o(k)\), so same-colour projections of heavy stars have total mass \(o(k)\) and close \(o(k^2)\) pairs.

Opposite-colour projections: the sets \(\pi_B(X_v(I))\) for \(v\in H_I\cap V_R\) have small pairwise intersections by \(\mathcal{D}\). Their sizes \(x_v\) are at most the product degree \((1+o(1))pn\), and their total mass is at most \(k-\ell_R+o(k)\) (vertices of \(I\) that are not accounted for by a new red name). The function \(x\mapsto\binom{x}{2}\) is convex, so for a fixed sum the binomial sum is maximized by putting as much mass as possible onto as few coordinates as possible, each of size at most \(pn\). That maximum is exactly the displayed minimum.

**Definition 11.5 (the open-pair function).**

\begin{align*}
f(\ell_R,\ell_B)
&\;=\;
\binom{\ell_R}{2}+\binom{\ell_B}{2}\\
&\quad
-\min\Bigl\{\binom{k-\ell_R}{2},\;\binom{pn}{2}+\binom{k-\ell_R-pn}{2}\Bigr\}\\
&\quad
-\min\Bigl\{\binom{k-\ell_B}{2},\;\binom{pn}{2}+\binom{k-\ell_B-pn}{2}\Bigr\}.
\end{align*}

**Corollary 11.6.**
After revealing edges incident to names outside \(\pi_R(I)\cup\pi_B(I)\) (and a negligible set of heavy names inside), at least \(f(\ell_R,\ell_B)-O(\varepsilon_1 k^2)\) pairs inside the two projections are still open.

The first two binomials are “all pairs among the red names, plus all pairs among the blue names.” The two minima are the heavy-star subtractions.

---

## 12. No large independent set

Write \(x_R=\ell_R/k\) and \(x_B=\ell_B/k\) for the **relative projection sizes**, numbers in \((0,1]\).

### 12.1 One set is unlikely to be independent

**Theorem 12.1 (one \(k\)-set; HHKP Lemma 4.1).**
Condition on \(\lvert\pi_R(I)\rvert=\ell_R\), \(\lvert\pi_B(I)\rvert=\ell_B\), and on the typicality / bucket events. Then

\[
\mathbb{P}(I\text{ is independent in }G)
\;\le\;
(1-p)^{f(\ell_R,\ell_B)-O(\varepsilon_1 k^2)}
\;\le\;
\exp\bigl(-p(f(\ell_R,\ell_B)-O(\varepsilon_1 k^2))\bigr).
\]

**Proof.**
For \(I\) to be independent, every still-open red or blue pair must be absent from the corresponding seed. Each such pair is a potential seed-edge, present independently with probability \(p\). The probability they are all absent is \((1-p)^{\#\text{open}}\). Use Lemma 1.2.

(The paper’s actual Lemma 4.1 is slightly more careful: a few open pairs might still be closed by the opposite colour after the remaining seed edges are revealed. Those extra closings are bounded by the light/medium theorems and absorbed into the \(\varepsilon_1 k^2\) budget. The lex order is used so that, when a pair is examined, one already knows whether it is “forward-closed” by the same colour.)

### 12.2 How rare is a given projection shape?

**Lemma 12.2 (shape probability; HHKP Lemma 4.2, first display).**
If \(\pi\) is a uniform injection, then

\[
\mathbb{P}\bigl(\lvert\pi_R(I)\rvert=\ell_R\text{ and }\lvert\pi_B(I)\rvert=\ell_B\bigr)
\;\le\;
\exp\Bigl(-\frac{2-x_R-x_B}{2}(1+o(1))\,k\log n\Bigr).
\]

**Proof.**
\(\pi(I)\) is a uniform random \(k\)-subset of the \(m\times m\) grid \(V_R\times V_B\). The number of \(k\)-sets using only \(\ell_R\) red names and \(\ell_B\) blue names is at most \(\binom{m}{\ell_R}\binom{m}{\ell_B}\binom{\ell_R\ell_B}{k}\). Divide by \(\binom{m^2}{k}\) and apply Lemma 1.1. Using \(m=n/\log^2 n\) and \(\ell_R=x_R k\), the dominant term is \(n^{-\frac12(2-x_R-x_B)k}\).

Also, by Lemma 1.1,

\[
\binom{n}{k}\;\le\;\Bigl(\frac{en}{k}\Bigr)^k
=\exp\bigl(k\log(en/k)\bigr)
=\exp\bigl(\tfrac12 k\log n+o(k\log n)\bigr),
\]

because \(n/k\sim\sqrt{n/\log n}\) and \(\log(n/k)=\tfrac12\log n+O(\log\log n)\).

### 12.3 Three cases

**Theorem 12.3 (union bound over shapes; HHKP Lemma 4.2).**
For a fixed \(k\)-set \(I\),

\[
\mathbb{P}(I\text{ independent and typical})
\;=\;
o\Bigl(\binom{n}{k}^{-1}\Bigr).
\]

**Proof.**
The left-hand side, times \(\binom{n}{k}\), is at most a \(k^2\)-factor (the number of shapes) times the maximum over shapes of

\[
\mathbb{P}(I\text{ independent}\mid\text{shape})
\cdot
\mathbb{P}(\text{shape})
\cdot\binom{n}{k}.
\]

We show this product is \(o(1)\) in every case.

**Case A: both projections are small,** \(x_R+x_B\le 1-\varepsilon/2\).

We do not need the seeds. Lemma 12.2 already gives

\[
\mathbb{P}(\text{shape})\cdot\binom{n}{k}
\;\le\;
\exp\bigl(-\Omega(\varepsilon\,k\log n)\bigr)
\;=\;o(1).
\]

**Case B: both projections are large,** \(x_R+x_B\ge 1+\varepsilon/2\).

Even after subtracting the heavy-star minima in the crudest way (replace each min by \(\binom{k-\ell}{2}\)),

\[
f(\ell_R,\ell_B)
\;\ge\;
\binom{\ell_R}{2}+\binom{\ell_B}{2}-\binom{k-\ell_R}{2}-\binom{k-\ell_B}{2}-o(k^2).
\]

The identity \(\binom{xk}{2}-\binom{(1-x)k}{2}=(x-\tfrac12)k^2+O(k)\) gives \(f\ge(x_R+x_B-1)k^2+O(k)\). Then

\[
p\,f
\;\ge\;
\beta\sqrt{\frac{\log n}{n}}\cdot(x_R+x_B-1)k^2
\;=\;
\beta\kappa(x_R+x_B-1)\,k\log n,
\]

because \(k^2\sqrt{\log n\,/\,n}=\kappa\,k\log n\). (Check: \(k=\kappa\sqrt{n\log n}\), so \(k^2=\kappa^2 n\log n\) and \(k^2\sqrt{\log n\,/\,n}=\kappa^2\sqrt{n\log n}\,\log n=\kappa\,k\log n\).)

With \(\beta=\tfrac12\) and \(\kappa=1+\varepsilon\),

\[
p\,f-\tfrac12(x_R+x_B-1)k\log n
\;=\;
\tfrac{\varepsilon}{2}(x_R+x_B-1)k\log n.
\]

The shape being large *helps* the adversary (more \(k\)-sets have large projections). That extra probability is exactly cancelled by the \(\tfrac12 k\log n\) coming from \(\binom{n}{k}\), and the leftover \(\varepsilon(x_R+x_B-1)/2\) is strictly positive in this case.

**This is why \(\beta=\tfrac12\) is admissible.** If you tried \(\beta<\tfrac12\), the leftover in Case B would change sign for \(x_R+x_B\) close to \(1\), and the union bound would fail.

**Case C: the projections sit near the diagonal,** \(1-\varepsilon/2<x_R+x_B<1+\varepsilon/2\).

The crude subtraction \(\binom{k-\ell}{2}\) is too pessimistic for the *smaller* projection: that projection is at most about \(\tfrac12\), so \(k-\ell_B>pn\) and the other branch of the min applies. That is a *smaller* subtraction, so \(f\) is larger than in the crude bound, which pays for the fact that \(x_R+x_B-1\) may be slightly negative. Expanding with \(\beta=\tfrac12\) and \(\kappa=1+\varepsilon\) produces an exponent \(-\Omega(\varepsilon\,k\log n)\) still. (This is the longest display in the paper’s Lemma 4.2; every term is a product of \(\beta,\kappa,x_R,x_B\). The sign is checked by using \(x_B\le(x_R+x_B)/2<(1+\varepsilon)/2\).)

### 12.4 Finish

**Theorem 12.4 (Theorem A, restated).**
For every \(\varepsilon>0\) and all large \(n\), there exists a triangle-free \(n\)-vertex graph with \(\alpha<(1+\varepsilon)\sqrt{n\log n}\).

**Proof.**
Let \(\mathcal{R}\) be the event that the configuration is typical and all three small buckets are well-behaved for every \(k\)-set. Then \(\mathbb{P}(\mathcal{R}^c)=o(1)\) by Theorems 9.2, 11.2, and 11.3.

Let \(X\) be the number of \(k\)-sets that are independent in \(G\). Then

\[
\mathbb{E}[X\cdot\mathbf{1}_{\mathcal{R}}]
=\sum_{\lvert I\rvert=k}\mathbb{P}(I\text{ independent and }\mathcal{R})
=o(1)
\]

by Theorem 12.3. So \(\mathbb{P}(X\ge 1)\le\mathbb{P}(\mathcal{R}^c)+\mathbb{E}[X\cdot\mathbf{1}_{\mathcal{R}}]=o(1)\) by Lemma 6.4. Therefore whp \(\alpha(G)<k\). The graph is triangle-free by Theorem 8.2.

**Corollary 12.5 (Theorem B).**
\(R(3,k)\ge(\tfrac12+o(1))k^2/\log k\).

**Proof.**
Theorem 12.4 plus Theorem 4.1.

---

## 13. What the paper does *not* say

| Statement | Status |
|---|---|
| \(R(3,k)\ge(\tfrac12+o(1))k^2/\log k\) | **Theorem** (this paper) |
| There exists a triangle-free \(n\)-vertex graph with \(\alpha<(1+\varepsilon)\sqrt{n\log n}\) | **Theorem**, random construction, whp |
| The same bound for a graph you can write down in time \(\mathrm{poly}(n)\) | **Not proved** here |
| \(R(3,k)\le(\tfrac12+o(1))k^2/\log k\) | **Conjecture.** This is an *upper* bound. |
| \(R(3,k)\le(1+o(1))k^2/\log k\) | **Theorem** (Shearer 1983) |

A random construction is a valid existence proof. It is not an algorithm that, on input \(n\), prints the adjacency list in polynomial time.

**Why \(\tfrac12\) looks tight (heuristic, not a proof).**
In any triangle-free graph, \(\alpha\ge\Delta\) (Theorem 2.7). This construction has \(\alpha\sim\Delta\sim\sqrt{n\log n}\): degree and independence number match, as they do in a random graph of the same density. Beating \(\tfrac12\) would require a triangle-free graph that is *sparser* than this *and* still has \(\alpha\) as small as a random graph of that smaller density.

Spectral methods cannot reach this bound: the Lovász \(\vartheta\)-function of every triangle-free \(n\)-vertex graph is \(\Omega(\sqrt{n})\), so any proof that bounds \(\alpha\) through \(\vartheta\) is stuck at Alon’s explicit scale \(R(3,k)=\Omega(k^{3/2})\).

---

## 14. A picture of the whole argument

```
two random seeds G_R, G_B on m = n / log² n vertices
density p = (1/2) √(log n / n)
        │
        ▼
label each of n final vertices by a unique pair (red name, blue name)
        │
        ▼
red edge  ⇔  red names adjacent
blue edge ⇔  blue names adjacent
        │
        ▼
delete one edge from every triangle, by a fixed lex rule     (Theorem 8.2)
        │
        ▼
output is triangle-free, average degree ~ √(n log n)
        │
        ▼
for each k-set I, light/medium/large stars close only o(k²) pairs
heavy stars are controlled by the two projection sizes          (§11)
        │
        ▼
remaining open pairs must all be missing from the seeds
probability ≤ (1-p)^{Θ(k²)}                                     (Theorem 12.1)
        │
        ▼
union bound over all k-sets is o(1)     ⇒     some output has α < k
        │
        ▼
R(3,k) > n  ~  k² / (2 log k)                                   (Theorem 4.1)
```

---

## 15. Glossary

| Term | Meaning |
|---|---|
| vertex, edge | the points and pairs of a graph |
| triangle | three mutual neighbours |
| independent set | a set with no edge inside it |
| \(\alpha(G)\) | size of a largest independent set |
| \(\Delta(G)\) | maximum degree |
| triangle-free | no triangle |
| \(R(3,k)\) | least \(N\) so that every \(N\)-vertex graph has a triangle or an independent \(k\)-set |
| \(G(n,p)\) | random graph, each edge present with probability \(p\) |
| seed / bite | one of the two small random graphs \(G_R,G_B\) |
| fibre \(F(v)\) | final vertices sharing a red (or blue) name \(v\) |
| open pair | a pair in \(I\) with no common product-neighbour yet |
| closed pair | a pair already sitting in some star \(X_v(I)\) |
| cleanup | the deterministic four-rule deletion that kills all triangles |
| whp | probability \(1-o(1)\) as \(n\to\infty\) |
| SOTA | state of the art: here, the constant \(\tfrac12\) in the *lower* bound |
| explicit | a deterministic \(\mathrm{poly}(n)\)-time construction of the graph |

---

## 16. How to read the paper after these notes

1. **Section 2** of HHKP — the construction (our §7–§8). You can now read it line by line.
2. **Lemma 3.1** — typical degrees. Treat as a Chernoff + union bound black box the first time.
3. **Lemma 3.2** — large stars. Read in full; it is purely combinatorial (our Theorem 11.1).
4. **Lemmas 3.3–3.4** — medium and light stars (our Theorems 11.2–11.3).
5. **Lemma 3.5** — heavy stars and the function \(f\) (our Theorem 11.4).
6. **Lemmas 4.1–4.2** — the independence probability and the three-case calculus (our §12). This is where \(\beta=\tfrac12\) is used.
7. **Section 6** — why they believe \(\tfrac12\) is tight. Heuristic, not a proof.

If one step of §12 Case C is still opaque, that is the longest calculation in the paper; write \(x_B\le x_R\) and expand \(p\cdot f\) as a quadratic polynomial in \(x_R,x_B\). Every coefficient is a number built from \(\beta=\tfrac12\) and \(\kappa=1+\varepsilon\).
