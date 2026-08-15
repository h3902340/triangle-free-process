# A beginner’s guide to the SOTA paper on \(R(3,k)\)

This note explains the 2025 paper

> Zion Hefty, Paul Horn, Dylan King, Florian Pfender,
> *Improving \(R(3,k)\) in just two bites*,
> [arXiv:2510.19718](https://arxiv.org/abs/2510.19718).

You do not need to be a Ramsey theorist. Every word that has a technical meaning is defined before it is used. Proofs are written as a sequence of small claims. When a step uses a standard probability inequality, the inequality is stated in English first, then applied.

**What the paper proves (a theorem):**

\[
R(3,k)\;\ge\;\Bigl(\tfrac12+o(1)\Bigr)\frac{k^2}{\log k}.
\]

**What the paper does *not* prove:** that \(\tfrac12\) is the exact constant. The matching *upper* bound \(R(3,k)\le(1+o(1))k^2/\log k\) is older (Shearer, 1983). Closing the gap from \(1\) down to \(\tfrac12\) is a conjecture, not a theorem.

All logarithms here are natural logs (base \(e\)), as in the paper. The symbol \(o(1)\) means “a quantity that goes to \(0\) as \(k\) (or \(n\)) goes to infinity.”

---

## How to read this guide

| If you want… | Read |
|---|---|
| The words “graph”, “triangle”, “independent set”, “Ramsey number” | §1 |
| Why a lower bound on \(R(3,k)\) is the same as a triangle-free graph with no large independent set | §2 |
| Why the constant \(\tfrac12\) appears | §3 |
| The history in one page | §4 |
| The two-bites construction, with every parameter defined | §5–§6 |
| Why the output is triangle-free | §7 |
| Why a large set is unlikely to stay independent | §8–§10 |
| What is still open, and how this repository relates | §11–§12 |

A first pass can stop after §7. Sections 8–10 are the actual SOTA proof.

---

## 1. Graphs, in the language of this paper

### 1.1 Graph, vertex, edge

A **graph** \(G\) is a finite set \(V(G)\) of **vertices** together with a set \(E(G)\) of **edges**. An edge is an unordered pair of distinct vertices. We never allow loops (an edge from a vertex to itself) unless we say so.

Two vertices are **adjacent**, or **neighbours**, if they form an edge. The **degree** of a vertex is the number of neighbours it has. The **maximum degree** is written \(\Delta(G)\). The **average degree** is \(2|E(G)|/|V(G)|\).

**Example.** Three vertices \(a,b,c\) with edges \(ab,bc\) is a path of length 2. Adding the edge \(ca\) makes a triangle.

### 1.2 Triangle, clique, independent set

A **triangle** is three vertices with all three pairs present as edges. In symbols: a copy of \(K_3\).

A **clique** of size \(\ell\) is \(\ell\) vertices with every pair joined by an edge. A triangle is a clique of size 3.

An **independent set** is a set of vertices with *no* edge inside it. The **independence number** \(\alpha(G)\) is the size of a largest independent set.

These two notions are complementary: an independent set in \(G\) is a clique in the **complement** (the graph with the same vertices and the complementary edges).

### 1.3 Triangle-free graphs have independent neighbourhoods

This one-line fact is used constantly.

**Lemma (neighbourhoods are independent).**
If \(G\) has no triangle, then for every vertex \(v\) the neighbourhood \(N(v)\) is an independent set. In particular \(\alpha(G)\ge\Delta(G)\).

**Proof.** If two neighbours \(x,y\) of \(v\) were adjacent, then \(\{v,x,y\}\) would be a triangle. So \(N(v)\) has no edges. It is an independent set of size \(\deg(v)\). Taking a vertex of maximum degree gives \(\alpha(G)\ge\Delta(G)\).

So in a triangle-free graph you cannot make degrees large without automatically creating a large independent set. Any construction that wants *small* \(\alpha\) must also keep degrees from being much larger than \(\alpha\).

### 1.4 The random graph \(G(n,p)\)

\(G(n,p)\) is the probability space of all graphs on \(n\) labelled vertices in which each possible edge is included independently with probability \(p\).

Typical facts we will use only as intuition (the SOTA proof never needs the full theory):

- Expected degree of a vertex is \(p(n-1)\approx pn\).
- If \(p\) is not tiny, a typical independent set has size about \((2\log(np))/p\).

---

## 2. What \(R(3,k)\) is, and how one proves a lower bound

### 2.1 Definition

**Definition (off-diagonal Ramsey number).**
\(R(3,k)\) is the smallest integer \(N\) such that *every* graph on \(N\) vertices contains either a triangle or an independent set of size \(k\).

Equivalently (pass to the complement, or colour the edges of \(K_N\) red/blue):

> \(R(3,k)\) is the smallest \(N\) such that every red/blue colouring of the edges of the complete \(N\)-vertex graph contains a red triangle or a blue clique of size \(k\).

The two views are the same: let red edges be the edges of \(G\). A red triangle is a triangle in \(G\). A blue \(k\)-clique is an independent set of size \(k\) in \(G\).

**Tiny exact values** (only for orientation; the paper is about large \(k\)):

- \(R(3,3)=6\). Among 5 vertices you can have a 5-cycle, which is triangle-free and has \(\alpha=2\). Among 6 vertices you cannot.
- \(R(3,4)=9\), \(R(3,5)=14\). Exact values stop being easy very quickly.

### 2.2 The dictionary: lower bound \(\Leftrightarrow\) a graph

To prove \(R(3,k)>n\) it is enough to exhibit **one** graph on \(n\) vertices that is triangle-free and has \(\alpha<k\).

**Lemma (the dictionary).**
The following are equivalent, for integers \(n,k\ge 2\):

1. There exists a triangle-free graph on \(n\) vertices with \(\alpha(G)<k\).
2. \(R(3,k)>n\).

**Proof.**
\((1)\Rightarrow(2)\). The graph in (1) is an \(n\)-vertex graph with no triangle and no independent set of size \(k\). So the “every \(N\)-vertex graph has a triangle or an independent \(k\)-set” statement fails at \(N=n\). Hence the smallest such \(N\) is at least \(n+1\).
\((2)\Rightarrow(1)\). If \(R(3,k)>n\), then it is not true that every \(n\)-vertex graph has a triangle or an independent \(k\)-set. So some \(n\)-vertex graph has neither: it is triangle-free and \(\alpha<k\).

The whole SOTA paper is a construction of such a graph, for

\[
k=(1+\varepsilon)\sqrt{n\log n},
\]

with \(\varepsilon>0\) arbitrary and \(n\) large. The next section turns that into the formula with \(\tfrac12\).

---

## 3. Why the constant is \(\tfrac12\)

This is algebra, not graph theory. It is the most common place a newcomer gets lost.

### 3.1 From \(\alpha<\sqrt{n\log n}\) to \(n\sim k^2/(2\log k)\)

**Claim.**
Suppose that for every \(\varepsilon>0\) and all large \(n\) there is a triangle-free \(n\)-vertex graph with

\[
\alpha(G)<(1+\varepsilon)\sqrt{n\log n}.
\]

Then

\[
R(3,k)\;\ge\;\Bigl(\tfrac12+o(1)\Bigr)\frac{k^2}{\log k}.
\]

**Proof.**
Fix \(\varepsilon>0\). For large \(n\), the dictionary and the hypothesis give

\[
R\bigl(3,\,(1+\varepsilon)\sqrt{n\log n}\bigr)\;>\;n.
\]

Set \(k=(1+\varepsilon)\sqrt{n\log n}\). Then \(k^2=(1+\varepsilon)^2\,n\log n\), so

\[
n=\frac{k^2}{(1+\varepsilon)^2\log n}.
\]

We only need to replace \(\log n\) by \(2\log k\). From \(k=(1+\varepsilon)\sqrt{n\log n}\) we have \(n\to\infty\) as \(k\to\infty\), and

\[
\log k=\log(1+\varepsilon)+\tfrac12\log n+\tfrac12\log\log n,
\]

so \(\log n=(2+o(1))\log k\). Therefore

\[
n=\frac{k^2}{(1+\varepsilon)^2\cdot(2+o(1))\log k}
=\frac{1}{2(1+\varepsilon)^2+o(1)}\cdot\frac{k^2}{\log k}.
\]

Since \(\varepsilon>0\) was arbitrary, the constant in front of \(k^2/\log k\) can be taken as any number strictly less than \(\tfrac12\), which is what \(\tfrac12+o(1)\) means on the lower-bound side (more precisely: the liminf of \(R(3,k)\cdot(\log k)/k^2\) is at least \(\tfrac12\)).

**Where the \(2\) comes from.** \(k\) is about \(\sqrt{n\log n}\), so \(n\) is about \(k^2/\log n\). But \(\log n\) is about \(2\log k\), because \(n\) is about \(k^2\). That factor \(2\) is the \(\tfrac12\).

### 3.2 Matching this against Shearer’s upper bound

Shearer proved that every triangle-free \(n\)-vertex graph of average degree \(d\) has

\[
\alpha(G)\;\ge\;(1+o_d(1))\,n\,\frac{\log d}{d}.
\]

A triangle-free graph also has \(\alpha(G)\ge\Delta(G)\ge d\) if one uses a regular (or nearly regular) example, or more carefully \(\alpha\ge\Delta\). Optimising \(d\) against those two lower bounds produces

\[
R(3,k)\;\le\;(1+o(1))\frac{k^2}{\log k}.
\]

So the SOTA *sandwich* is

\[
\Bigl(\tfrac12+o(1)\Bigr)\frac{k^2}{\log k}
\;\le\;
R(3,k)
\;\le\;
(1+o(1))\frac{k^2}{\log k}.
\]

The lower bound is HHKP. The upper bound is Shearer. The conjecture of Campos–Jenssen–Michelen–Sahasrabudhe (and of HHKP) is that the truth is the lower bound: the extra factor \(2\) on the upper side should go away. **That conjecture is an upper-bound problem.** The SOTA paper does not touch it.

### 3.3 Why you should expect \(\alpha\sim\sqrt{n\log n}\)

In a triangle-free graph, \(\alpha\ge\Delta\). If the graph is also as dense as a random graph of the same average degree, one expects \(\alpha\) to be on the same scale as the degree.

HHKP builds a triangle-free graph with average degree

\[
(1+o(1))\sqrt{n\log n}
\]

and proves \(\alpha<(1+\varepsilon)\sqrt{n\log n}\). Degree and independence number match. Any improvement of the constant \(\tfrac12\) would need a triangle-free graph that is *sparser* than this *and* still has \(\alpha\) as small as a random graph of that smaller density. The paper explains why that looks unlikely.

---

## 4. One page of history

| Year | Result | Method |
|---|---|---|
| 1930 | \(R(\ell,k)\) exists | Ramsey |
| 1980–83 | \(R(3,k)=O(k^2/\log k)\) | Ajtai–Komlós–Szemerédi; Shearer makes the constant \(1\) |
| 1995 | \(R(3,k)\ge c\,k^2/\log k\) with \(c\approx 1/160\) | Kim, nibble |
| 2013 | \(c=\tfrac14\) | Bohman–Keevash and Fiz Pontiveros–Griffiths–Morris: the **triangle-free process** |
| 2025 | \(c=\tfrac13\) | Campos–Jenssen–Michelen–Sahasrabudhe (CJMS) |
| 2025 | \(c=\tfrac12\) | HHKP, **two bites** |

The **triangle-free process** starts from the empty graph and repeatedly adds a uniformly random edge that does not create a triangle, until none remain. Analysing it requires tracking many random variables along a differential equation and proving they concentrate. It is long.

CJMS improved the constant to \(\tfrac13\) by a different random construction: a sparse random graph on fewer vertices, blown up, then a nibble to kill the independent sets created by the blow-up.

HHKP’s idea is: **do the blow-up twice, in two colours, and overlay them at random.** Each copy destroys the leftover independent sets of the other. Triangles appear, but they come in large bunches sharing an edge, so a cheap deterministic cleanup removes them. There is no nibble and no differential equation. The analysis uses only Chernoff bounds and McDiarmid’s bounded-differences inequality.

---

## 5. The idea, before the symbols

Think of two sparse random graphs, a **red** one and a **blue** one, each on only \(m=n/\log^2 n\) vertices. Each is sparse enough that a random graph of that density has almost no triangles (below the “deletion threshold” \(p\sim 1/\sqrt{m}\)).

Blow each of them up by a factor \(s=\log^2 n\): replace every vertex by \(s\) copies. You get two triangle-free \(n\)-vertex graphs, each with a decent number of edges, but each with huge independent sets (a whole blown-up vertex).

Now overlay them using a random matching of vertices: every final vertex is labelled by one red name and one blue name. Put a red edge between two final vertices when their red names are adjacent, and a blue edge when their blue names are adjacent.

- A set that was independent in the red blow-up is typically *not* independent in blue, and vice versa.
- New triangles appear. The important geometric fact: many of those triangles share an edge (they sit in a common “star”). Deleting that one edge kills many triangles at once. That is the efficiency gain over ordinary “delete one edge from each triangle.”

Finally, delete a few edges by a fixed rule so that no triangle remains. The remaining graph is triangle-free, still reasonably dense, and — this is the hard part — has no independent set of size \((1+\varepsilon)\sqrt{n\log n}\).

---

## 6. The construction, with every parameter defined

Fix \(\varepsilon\in(0,1/100)\) and a large integer \(n\). All \(o(1)\) statements are as \(n\to\infty\).

### 6.1 Parameters

| Symbol | Value | Meaning |
|---|---|---|
| \(s\) | \(\log^2 n\) | blow-up factor; also typical fibre size |
| \(m\) | \(n/s=n/\log^2 n\) | number of red (resp. blue) names |
| \(p\) | \(\beta\sqrt{\log n\,/\,n}\) | edge probability in each seed graph |
| \(\beta\) | \(\tfrac12\) | the density constant that produces SOTA \(\tfrac12\) |
| \(k\) | \(\kappa\sqrt{n\log n}\) | forbidden independent-set size |
| \(\kappa\) | \(1+\varepsilon\) | a little larger than \(1\), so the algebra has room |
| \(\varepsilon_2\ll\varepsilon_1\ll\varepsilon\) | tiny positive constants | error budgets in the typicality and bucket lemmas |

The paper writes \(m\) for what some notes in this repository call \(N\).

### 6.2 Two seed graphs

Let \(V_R=\{r_1,\dots,r_m\}\) and \(V_B=\{b_1,\dots,b_m\}\) be disjoint.

Let \(G_R\) be a random graph \(G(m,p)\) on \(V_R\) (the **red seed**).
Let \(G_B\) be an independent copy of \(G(m,p)\) on \(V_B\) (the **blue seed**).

These two graphs are *not* the final graph. They are small and still have a few triangles; that will not matter, because triangles in the seeds become monochromatic triangles in the product and are deleted by the cleanup.

### 6.3 Random labels

Let \(V(G)=\{v_1,\dots,v_n\}\) be the final vertex set.

Choose an injection

\[
\pi:V(G)\hookrightarrow V_R\times V_B
\]

uniformly at random among all injective maps. Write

\[
\pi(v)=(\pi_R(v),\,\pi_B(v)).
\]

So each final vertex has a **red name** \(\pi_R(v)\in V_R\) and a **blue name** \(\pi_B(v)\in V_B\), and no two final vertices share the same pair of names.

**Definition (fibre).**
For \(r\in V_R\), the **red fibre** is \(F(r)=\pi_R^{-1}(r)\), the set of final vertices with red name \(r\). Blue fibres are defined the same way. Typically \(|F(r)|\approx s=\log^2 n\).

### 6.4 The product edges (before cleanup)

Put a **red edge** between distinct \(u,v\in V(G)\) when \(\pi_R(u)\pi_R(v)\) is an edge of \(G_R\).
Put a **blue edge** when \(\pi_B(u)\pi_B(v)\) is an edge of \(G_B\).

A pair may receive both colours; the paper keeps both and works with a multigraph. Independence number does not care about multiplicity, so this is only a bookkeeping convenience.

In product language: the host graph is the **co-normal (strong-or) product** \(G_R\boxtimes G_B\) on \(V_R\times V_B\), and the construction is a random \(n\)-vertex induced subgraph of that product.

### 6.5 Neighbourhoods in the product

For \(r_i\in V_R\) write \(N(r_i)\) for its neighbourhood in the *seed* \(G_R\), and

\[
N_{r_i}\;=\;\bigcup_{r_j\in N(r_i)} F(r_j)
\]

for the set of final vertices whose red name is a \(G_R\)-neighbour of \(r_i\). This is the red neighbourhood, in the product, of any final vertex named \(r_i\).

The **forward** neighbourhood \(N_{r_i}^+\) keeps only neighbours \(r_j\) with \(j>i\). That extra order is used when the cleanup deletes the *last* edge of a monochromatic triangle.

---

## 7. Cleanup: why the output is triangle-free

This step is completely deterministic. No coin is flipped.

Order all pairs in \(V_R\) lexicographically (first by the smaller index, then the larger). Do the same for \(V_B\).

**Construction (cleanup).**
Start from the red and blue product edges. Then:

1. **Monochromatic red triangles.** In every red triangle, look at the three red names of its three edges. Delete the red product-edge whose red name-pair comes *last* in the lex order.
2. **Monochromatic blue triangles.** The same, using blue names.
3. **Two red, one blue.** Delete the blue edge.
4. **Two blue, one red.** Delete the red edge.

**Lemma (the output is triangle-free).**
After these four rules, no triangle remains.

**Proof.**
A triangle in the product uses some combination of red and blue edges.

- Three red edges: rule 1 deleted one of them.
- Three blue edges: rule 2 deleted one of them.
- Two red and one blue: rule 3 deleted the blue edge.
- Two blue and one red: rule 4 deleted the red edge.
- Three edges that are both colours: then in particular there is a red triangle and a blue triangle on the same three vertices, already destroyed by rules 1–2.

Those are all the colour patterns. So no triangle survives.

**Why this is cheap.**
A typical seed-vertex is the red name of about \(s=\log^2 n\) final vertices. A red seed-edge therefore lifts to about \(s^2\) product-edges, and a monochromatic red triangle in the seed lifts to a huge bunch of product-triangles that all share the “last” edge in the lex order. Deleting that one product-edge (or, in the paper’s formulation, deleting the last edge in each such triangle) removes many triangles at once. Ordinary edge-deletion, which spends one deletion per triangle, cannot afford the density \(p\sim\sqrt{\log n\,/\,n}\). The factor \(s\) is exactly the gain.

The paper’s Lemma 3.1 says that with probability \(1-o(1)\) the fibres, degrees, and codegrees are all close to their means. On that event the number of deleted edges is a small fraction of the total, and the final average degree is still \((2+o(1))p\cdot n=(1+o(1))\sqrt{n\log n}\).

---

## 8. Open pairs, closed pairs, and stars

To show \(\alpha(G)<k\) one must show that a typical \(k\)-set \(I\subset V(G)\) is *not* independent in the cleaned graph.

### 8.1 Definitions

Fix a set \(I\subset V(G)\) with \(|I|=k\).

**Definition (star of a name).**
For \(v\in V_R\cup V_B\), write

\[
X_v(I)\;=\;I\cap N_v.
\]

This is the set of vertices of \(I\) that are product-neighbours of the fibre of \(v\). The pairs among \(X_v(I)\) are the pairs of \(I\) that \(v\) **closes**: they already have a common neighbour (the fibre of \(v\)), so putting an edge between them would complete a triangle with that neighbour.

**Definition (closed and open pairs).**

\[
C(I)\;=\;\bigcup_{v\in V_R\cup V_B}\binom{X_v(I)}{2},
\qquad
O(I)\;=\;\binom{\pi(I)}{2}\setminus C(I).
\]

A pair inside \(I\) is **closed** if some name \(v\) already witnesses a common neighbour in the product. It is **open** otherwise.

Cleanup can delete edges, but it cannot *add* edges. So:

- a closed pair may or may not remain an edge after cleanup;
- an **open** pair, if it is present as a red or blue product-edge, will *survive* cleanup as an edge inside \(I\) (the paper’s Lemma 4.1 makes this precise with a lex-order case analysis). Therefore, for \(I\) to be independent, **every remaining open pair must be a non-edge of the seeds**.

That is the engine of the proof: count how many open pairs are left, and charge \((1-p)^{\#\text{open pairs}}\) for the event that they are all missing.

### 8.2 Four buckets

Not every closer \(v\) is equally dangerous. Split \(V_R\cup V_B\) by the size of \(X_v(I)\):

| Bucket | Size of \(X_v(I)\) | Name in the paper |
|---|---|---|
| \(H_I\) | \(>t_1=\sqrt{n\log n}/\log\log n\) | huge / heavy |
| \(L_I\) | \(t_2<|X_v|\le t_1\), \(t_2=n^{1/4+\varepsilon}\) | large |
| \(M_I\) | \(t_3<|X_v|\le t_2\), \(t_3=n^{2\varepsilon}\) | medium |
| \(S_I\) | \(\le t_3\) | small / light |

The number of pairs a vertex \(v\) closes is \(\binom{|X_v(I)|}{2}\). The proof shows:

- \(L_I\), \(M_I\), and \(S_I\) together close only \(o(k^2)\) pairs (a negligible fraction of all pairs in \(I\));
- the only serious contribution is \(H_I\), and that contribution is controlled by a convexity / majorization bound in terms of the projection sizes \(\ell_R=|\pi_R(I)|\) and \(\ell_B=|\pi_B(I)|\).

---

## 9. The bucket lemmas, proved

Throughout this section, \(\mathcal{D}\) is the “typical configuration” event of the paper’s Lemma 3.1: fibres have size \((1\pm\varepsilon_2)\log^2 n\), seed degrees are \((1\pm\varepsilon_2)pm\), seed codegrees are \(O(\log n)\), product degrees are \((1\pm\varepsilon_2)pn\), and product codegrees are \(O(\log^3 n)\). Chernoff plus a union bound over \(O(m^2)\) vertices and pairs give \(\mathbb{P}(\mathcal{D})=1-o(1)\). We work on \(\mathcal{D}\) unless stated otherwise.

### 9.1 Large stars (\(L_I\)): a deterministic double count

**Lemma (large stars close \(o(k^2)\) pairs).**
On \(\mathcal{D}\), for every \(k\)-set \(I\),

\[
\sum_{v\in L_I}\binom{|X_v(I)|}{2}\;=\;o(k^2).
\]

**Proof.**
We first show that \(L_I\) cannot be big. Take any subset \(L\subseteq L_I\). Inclusion-exclusion and the codegree bound \(|X_u\cap X_v|\le C\log^3 n\) give

\begin{align*}
k=|I|
&\;\ge\;
\Bigl|\bigcup_{v\in L}X_v(I)\Bigr|
\;\ge\;
\sum_{v\in L}|X_v|
-\sum_{\{u,v\}\subset L}|X_u\cap X_v|\\
&\;\ge\;
|L|\cdot n^{1/4+\varepsilon}
-\binom{|L|}{2}C\log^3 n.
\end{align*}

If \(|L|\) were as large as \(n^{(1-\varepsilon)/4}\), the first term would be \(\gg k\) and the second term would still be smaller, a contradiction. Hence \(|L_I|<n^{(1-\varepsilon)/4}\).

A second pass of the same count, now with this bound on \(|L_I|\), shows that the stars are almost disjoint:

\[
\sum_{v\in L_I}|X_v(I)|\;\le\;(1+o(1))k.
\]

Each star has size at most \(t_1=o(k)\), so

\[
\sum_{v\in L_I}\binom{|X_v|}{2}
\;\le\;
\frac{t_1}{2}\sum_{v\in L_I}|X_v|
\;=\;
o(k)\cdot k
\;=\;
o(k^2).
\]

No probability was used except the typicality event \(\mathcal{D}\).

### 9.2 Medium stars (\(M_I\)): an unusually dense bipartite graph

**Lemma (medium stars close \(o(k^2)\) pairs, with high probability).**
With probability \(1-o(1)\), every \(k\)-set \(I\) satisfies \(\sum_{v\in M_I}\binom{|X_v(I)|}{2}=o(k^2)\).

**Idea of the proof.**
If the medium stars of some \(I\) were heavy, the bipartite graphs

\[
\bigl(M_I\cap V_R,\;\pi_R(I)\bigr)
\quad\text{in }G_R
\qquad\text{and}\qquad
\bigl(M_I\cap V_B,\;\pi_B(I)\bigr)
\quad\text{in }G_B
\]

would have far more edges than a \(G(m,p)\) bipartite graph of those sizes is allowed to have.

A Chernoff bound says: the probability that a fixed bipartite pair \((B,I)\) is that dense is at most \(\exp(-n^{3/4-2\varepsilon})\). The number of candidate pairs \((B,I)\) is

\[
\binom{n}{k}\binom{2m}{O(kn^{1/4-3\varepsilon})}
=\exp\bigl(o(n^{3/4-2\varepsilon})\bigr).
\]

The union bound is \(o(1)\): there are not enough candidates to make up for how rare each dense fingerprint is.

Once the total medium mass \(\sum_{v\in M_I}|X_v|\) is \(O(k\,n^{1/4-\varepsilon})\), multiply by the maximum star size \(t_2=n^{1/4+\varepsilon}\) to get \(o(k^2)\) closed pairs.

### 9.3 Light stars (\(S_I\)): expectation plus bounded differences

**Lemma (light stars close \(o(k^2)\) pairs, with high probability).**
With probability \(1-o(1)\), every \(k\)-set \(I\) satisfies \(\sum_{v\in S_I}\binom{|X_v(I)|}{2}=o(k^2)\).

**Idea of the proof, in two pieces.**

*Inside the projections.* There are at most \(2k\) names in \(\pi_R(I)\cup\pi_B(I)\), and each light star has size \(\le n^{2\varepsilon}\), so those names close at most \(2k\cdot n^{4\varepsilon}\) pairs, which is \(o(k^2)\) because \(k\sim\sqrt{n\log n}\).

*Outside the projections.* For a pair of \(I\) that does not already sit in a common fibre, the probability that some outside name closes it is at most \(2p^2 m=2\beta^2/\log n=1/(2\log n)\) when \(\beta=\tfrac12\). So the *expected* number of light-closed pairs is only \(k^2/(4\log n)\), which is \(o(k^2)\).

To upgrade expectation to “every \(I\) at once”, use **McDiarmid’s inequality**: if a function of many independent inputs changes by at most \(c_i\) when the \(i\)-th input is edited, then deviations of size \(t\) have probability \(\exp(-t^2/(2\sum c_i^2))\). Here the inputs are the neighbourhoods of outside names, and editing one name changes the closed-pair count by at most \(\binom{n^{2\varepsilon}}{2}\). The resulting tail is so small that even after multiplying by the number \(\binom{n}{k}\) of candidate sets \(I\), the failure probability is \(o(1)\).

This is the step that is *not* elementary first-moment counting. At the SOTA scale \(|I|\sim\sqrt{n\log n}\), a first-moment bound \(\sum\binom{d}{2}\le t_3\cdot|I|\Delta\) is *not* \(o(k^2)\) unless \(t_3\) is tiny. The paper’s saving is this second-moment / bounded-differences argument over the random seeds.

### 9.4 Heavy stars (\(H_I\)): convexity

On \(\mathcal{D}\), the same double count as in §9.1 shows there are only \(O(\log\log n)\) heavy names, and their stars are almost disjoint. The pairs they close, after projection onto the opposite colour, are majorized by a vector whose entries are \(0\) or \(pn\): you cannot do worse than putting as much mass as possible onto as few stars as possible, each of size at most the product degree \(pn\).

The outcome is a deterministic bound: writing \(\ell_R=|\pi_R(I)|\) and \(\ell_B=|\pi_B(I)|\),

\[
\sum_{v\in H_I\cap V_R}\binom{|\pi_B(X_v(I))|}{2}
\;\le\;
(1+o(1))\min\Bigl\{\binom{k-\ell_R}{2},\;
\binom{pn}{2}+\binom{k-\ell_R-pn}{2}\Bigr\},
\]

and symmetrically with colours swapped.

**What this means in English.**
The heavy red names can close many *blue* pairs inside \(I\), but not more than:

- all pairs among the vertices of \(I\) that do *not* use a new red name (at most \(k-\ell_R\) such vertices), or
- the pairs inside one full product-neighbourhood plus the leftover, if that is smaller.

Those are the pairs you must *subtract* when you count open pairs.

### 9.5 The open-pair lower bound

Put the four buckets together. After revealing the edges that touch names outside \(\pi_R(I)\cup\pi_B(I)\) (and a negligible set of heavy names inside), at least

\[
f(\ell_R,\ell_B)-O(\varepsilon_1 k^2)
\]

pairs inside the two projections are still open, where

\begin{align*}
f(\ell_R,\ell_B)
&\;=\;
\binom{\ell_R}{2}+\binom{\ell_B}{2}\\
&\qquad
-\min\Bigl\{\binom{k-\ell_R}{2},\;\binom{pn}{2}+\binom{k-\ell_R-pn}{2}\Bigr\}\\
&\qquad
-\min\Bigl\{\binom{k-\ell_B}{2},\;\binom{pn}{2}+\binom{k-\ell_B-pn}{2}\Bigr\}.
\end{align*}

The first two binomials are “all pairs among the red names, plus all pairs among the blue names.” The two minima are the heavy-star subtractions of §9.4.

---

## 10. No large independent set

This is the paper’s Lemma 4.1–4.2 plus the final union bound. We first state the probability facts in English, then do the algebra that produces \(\beta=\tfrac12\).

### 10.1 One set is unlikely to be independent

**Lemma (one \(k\)-set).**
Condition on \(\pi_R(I)\) having size \(\ell_R\) and \(\pi_B(I)\) having size \(\ell_B\), and on the typicality / bucket events. The probability that \(I\) is independent in the cleaned graph is at most

\[
(1-p)^{f(\ell_R,\ell_B)-O(\varepsilon_1 k^2)}
\;\le\;
\exp\bigl(-p(f(\ell_R,\ell_B)-O(\varepsilon_1 k^2))\bigr).
\]

**Why.**
For \(I\) to be independent, every still-open red or blue pair must be absent from the corresponding seed. Each such pair is a potential seed-edge, present with probability \(p\), and the pairs are distinct. The probability they are all absent is \((1-p)^{\#\text{open}}\). (The paper’s actual Lemma 4.1 is slightly more careful: a few open pairs might still be closed by the opposite colour after the remaining seed edges are revealed. That error is absorbed into the \(\varepsilon_1 k^2\) budget by the light/medium lemmas.)

Use \(1-p\le e^{-p}\).

### 10.2 How rare is a given projection shape?

Write \(x_R=\ell_R/k\) and \(x_B=\ell_B/k\). These are the **relative projection sizes**, numbers in \((0,1]\).

A uniformly random injection \(\pi\) sends \(I\) to a random \(k\)-set in \(V_R\times V_B\). The probability that the red names use only \(\ell_R\) values and the blue names only \(\ell_B\) values is at most

\[
\exp\Bigl(-\frac{2-x_R-x_B}{2}(1+o(1))\,k\log n\Bigr).
\]

**Intuition.** If both projections are small (\(x_R+x_B\) much less than \(2\)), you are forcing \(k\) points into a small rectangle \(\ell_R\times\ell_B\) inside an \(m\times m\) grid. That is rare, and the formula measures how rare.

Also \(\binom{n}{k}=\exp\bigl(\tfrac12 k\log n+o(k\log n)\bigr)\), because \(k\sim\sqrt{n\log n}\) and Stirling’s bound \(\binom{n}{k}\le(en/k)^k\) gives \(\log\binom{n}{k}\le k\log(en/k)\sim k\cdot\tfrac12\log n\).

### 10.3 Three cases

The expected number of bad \(k\)-sets is at most \(\binom{n}{k}\) times the maximum, over shapes \((x_R,x_B)\), of

\[
\mathbb{P}(I\text{ independent}\mid\text{shape})
\cdot
\mathbb{P}(\text{shape}).
\]

We show this product is \(o\bigl(\binom{n}{k}^{-1}\bigr)\) in every case, so the expectation is \(o(1)\), so with high probability there is *no* independent \(k\)-set.

**Case A: both projections are small,** \(x_R+x_B\le 1-\varepsilon/2\).

We do not even need the seeds. The shape itself is rarer than \(\binom{n}{k}^{-1}\):

\[
\mathbb{P}(\text{shape})\cdot\binom{n}{k}
\;\le\;
\exp\bigl(-\Omega(\varepsilon\,k\log n)\bigr)
\;=\;o(1).
\]

**Case B: both projections are large,** \(x_R+x_B\ge 1+\varepsilon/2\).

Now there are many pairs among the names. Even after subtracting the heavy-star minima in the crudest way (replace each min by \(\binom{k-\ell}{2}\)), one has

\[
f(\ell_R,\ell_B)
\;\ge\;
\binom{\ell_R}{2}+\binom{\ell_B}{2}-\binom{k-\ell_R}{2}-\binom{k-\ell_B}{2}-o(k^2).
\]

A short expansion:

\[
\binom{xk}{2}-\binom{(1-x)k}{2}
=\bigl(x-\tfrac12\bigr)k^2+O(k),
\]

so

\[
f\;\ge\;\bigl(x_R+x_B-1\bigr)k^2+O(k).
\]

Then

\[
p\,f
\;\ge\;
\beta\sqrt{\frac{\log n}{n}}\cdot(x_R+x_B-1)k^2
\;=\;
\beta\kappa(x_R+x_B-1)\,k\log n,
\]

because \(k^2\sqrt{\log n\,/\,n}=\kappa^2 n\log n\cdot\sqrt{\log n\,/\,n}/\kappa^0=\kappa^2\sqrt{n\log n}\,\log n=\kappa\,k\log n\). With \(\beta=\tfrac12\) and \(\kappa=1+\varepsilon\),

\[
p\,f-\tfrac12(x_R+x_B-1)k\log n
\;=\;
\bigl(\tfrac12(1+\varepsilon)-\tfrac12\bigr)(x_R+x_B-1)k\log n
\;=\;
\tfrac{\varepsilon}{2}(x_R+x_B-1)k\log n.
\]

The shape-probability *gives back* a factor \(\exp\bigl(\tfrac12(x_R+x_B-1)k\log n\bigr)\) (the projection is *more* common when it is large). It is exactly cancelled by the \(\tfrac12\) coming from \(\binom{n}{k}\), and the leftover \(\varepsilon(x_R+x_B-1)/2\) is strictly positive in this case. The product is \(o\bigl(\binom{n}{k}^{-1}\bigr)\).

**This is why \(\beta=\tfrac12\) is admissible.** If you tried \(\beta<\tfrac12\), the leftover in Case B would change sign for \(x_R+x_B\) close to \(1\), and the union bound would fail.

**Case C: the projections sit near the diagonal,** \(1-\varepsilon/2<x_R+x_B<1+\varepsilon/2\).

Here the crude subtraction \(\binom{k-\ell}{2}\) is too pessimistic for the *smaller* projection: that projection is at most about \(1/2\), so \(k-\ell_B>pn\) and the other branch of the min,

\[
\binom{pn}{2}+\binom{k-\ell_B-pn}{2},
\]

is the one that applies. That is a smaller subtraction, so \(f\) is larger than in the crude bound, which pays for the fact that \(x_R+x_B-1\) may be slightly negative. The paper’s expansion (Lemma 4.2, third display) shows the exponent is \(-\Omega(\varepsilon\,k\log n)\) still.

### 10.4 Finish

**Theorem (HHKP).**
For every \(\varepsilon>0\) and all large \(n\), there exists a triangle-free \(n\)-vertex graph with \(\alpha<(1+\varepsilon)\sqrt{n\log n}\). Hence \(R(3,k)\ge(\tfrac12+o(1))k^2/\log k\).

**Proof.**
Let \(\mathcal{R}\) be the event that the configuration is typical and all three small buckets are well-behaved for every \(k\)-set. Then \(\mathbb{P}(\mathcal{R}^c)=o(1)\) by §9.

The probability that some \(k\)-set is independent is at most

\[
\mathbb{P}(\mathcal{R}^c)
+\sum_{|I|=k}\mathbb{P}(I\text{ independent and }\mathcal{R}).
\]

Each term in the sum is \(o\bigl(\binom{n}{k}^{-1}\bigr)\) by §10.3, and there are \(\binom{n}{k}\) terms, so the sum is \(o(1)\). Therefore with probability \(1-o(1)\) the cleaned graph has no independent \(k\)-set. It is triangle-free by §7. The dictionary of §2 and the algebra of §3 give the Ramsey bound.

---

## 11. What the paper does *not* say

| Statement | Status |
|---|---|
| \(R(3,k)\ge(\tfrac12+o(1))k^2/\log k\) | **Theorem** (HHKP) |
| There exists a triangle-free \(n\)-vertex graph with \(\alpha<(1+\varepsilon)\sqrt{n\log n}\) | **Theorem**, random construction, with high probability |
| The same bound for a graph you can write down in polynomial time | **Not proved** by HHKP |
| \(R(3,k)\le(\tfrac12+o(1))k^2/\log k\) | **Conjecture** (CJMS / HHKP). This is an *upper* bound. |
| Shearer’s \(R(3,k)\le(1+o(1))k^2/\log k\) | **Theorem** (1983) |

A random construction is a perfectly valid existence proof. It is not an algorithm that, on input \(n\), prints the adjacency list in time \(\mathrm{poly}(n)\).

Spectral methods cannot reach this bound: the Lovász \(\vartheta\)-function of every triangle-free \(n\)-vertex graph is \(\Omega(\sqrt{n})\), so any proof that bounds \(\alpha\) through \(\vartheta\) is stuck at the Alon scale \(R(3,k)=\Omega(k^{3/2})\).

---

## 12. How this repository talks about the same theorem

This repository studies *named* graphs that try to copy the HHKP template.

| Object | What it is | SOTA \(\alpha\) | Time |
|---|---|---|---|
| HHKP | random two bites | **theorem** (whp) | n/a |
| Counting rewrite (`sota-combinatorial.tex`) | the same proof, written as “fraction of configurations” instead of “probability” | **theorem** | n/a |
| **Family L** | the lexicographically first good HHKP configuration | **theorem** | exponential |
| **Family A** | two truncated-parabola Cayley graphs on \(\mathbb{F}_q^2\), sampled on an explicit shear, then cleaned | **conjectural** | \(\mathrm{poly}(n)\) |
| Alon Dual-BCH | a different explicit Cayley graph | only \(\Omega(k^{3/2})\) | \(\mathrm{poly}(n)\) |

Family L is a well-defined graph, and the counting proof shows a good configuration exists, so the lex-first one exists and has the SOTA bound. Finding it by brute force takes \(\exp(\Theta(n^2/\log^4 n))\) time.

Family A is a polynomial-time algorithm (`explicit_family.py --n`). It is proved to be triangle-free and of degree \(O(\sqrt{n\log n})\). The SOTA independence-number bound for Family A is **not** a theorem. The remaining gaps are recorded in [`EXPLICIT-STATUS.md`](EXPLICIT-STATUS.md).

A counting rewrite of HHKP is *not* an explicit construction: the tail bounds are still there, they are just phrased as “the fraction of bad configurations is small.”

---

## 13. A short glossary

| Term | Meaning |
|---|---|
| \(\alpha(G)\) | independence number: size of a largest edgeless set |
| \(\Delta(G)\) | maximum degree |
| triangle-free | no three mutual neighbours |
| \(R(3,k)\) | least \(N\) so that every \(N\)-vertex graph has a triangle or an independent \(k\)-set |
| \(G(n,p)\) | random graph, each edge present with probability \(p\) |
| seed / bite | one of the two small random graphs \(G_R,G_B\) |
| fibre \(F(v)\) | final vertices sharing a red (or blue) name \(v\) |
| open pair | a pair in \(I\) with no common product-neighbour yet |
| closed pair | a pair already sitting in some star \(X_v(I)\) |
| cleanup | the deterministic four-rule deletion that kills all triangles |
| whp | with high probability: probability \(1-o(1)\) as \(n\to\infty\) |
| SOTA | state of the art: here, the constant \(\tfrac12\) in the lower bound |
| explicit | a deterministic \(\mathrm{poly}(n)\)-time construction of the graph |
| \(o(1)\) | tends to \(0\) as the large parameter tends to infinity |
| Chernoff bound | a tail inequality for sums of independent \(\{0,1\}\) random variables |
| McDiarmid’s inequality | a tail inequality for functions with bounded differences |

---

## 14. If you want to read the paper next

The paper is short by the standards of this area. A sensible order:

1. **Section 2** of HHKP — the construction (our §6–§7).
2. **Lemma 3.1** — typical degrees and fibres. You can treat this as a black box the first time.
3. **Lemmas 3.2–3.4** — the three small buckets (our §9.1–§9.3). Lemma 3.2 is the one to read in full; it is purely combinatorial.
4. **Lemma 3.5** — heavy stars and the function \(f\) (our §9.4–§9.5).
5. **Lemmas 4.1–4.2** — the independence probability and the three-case calculus (our §10). This is where \(\beta=\tfrac12\) is used.
6. **Section 6** — why they believe \(\tfrac12\) is tight. This is heuristic, not a proof.

Companion notes in this repository:

- [`sota-combinatorial.tex`](sota-combinatorial.tex) — the same existence proof in counting language.
- [`PRESENTATION.md`](PRESENTATION.md) — an older, weaker bound (Bohman’s order of magnitude, not the constant \(\tfrac12\)).
- [`explicit-family.tex`](explicit-family.tex) — Family L and Family A.
- [`hhkp-conjecture.tex`](hhkp-conjecture.tex) — why the *upper* bound \(R(3,k)\le(\tfrac12+o(1))k^2/\log k\) is still open.

---

## 15. One picture of the whole argument

```
two random seeds G_R, G_B on m = n / log² n vertices, density p = (1/2) √(log n / n)
        │
        ▼
label each of n final vertices by a unique pair (red name, blue name)
        │
        ▼
put a red edge when red names are adjacent; a blue edge when blue names are adjacent
        │
        ▼
delete one edge from every triangle, by a fixed lex rule          (cleanup)
        │
        ▼
the output is triangle-free and has average degree ~ √(n log n)
        │
        ▼
for each k-set I, most pairs are still open after the small stars are subtracted
        │
        ▼
those open pairs must all be missing from the seeds, which has probability (1-p)^{Θ(k²)}
        │
        ▼
union bound over all k-sets is o(1)     ⇒     some output has α < (1+ε) √(n log n)
        │
        ▼
R(3,k) > n  ~  k² / (2 log k)
```
