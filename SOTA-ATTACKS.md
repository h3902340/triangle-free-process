# Attempts to beat the SOTA constants for \(R(3,k)\)

**Status: no unconditional breakthrough.** This note records the attacks that were tried and why they do not move either leading constant. It is not a theorem.

Round 2 attacked DJPR’s \(4/3\) ratio. Round 3 checked large-fugacity occupancy, DST variance bounds, maximality, and enumerated all triangle-free graphs on \(n\le 7\). Round 5 tested leftover-graph augmentation of a uniform independent set (the max-versus-average gap). Round 6 scanned leftover as a function of fugacity and every triangle-free inverse-closed circulant on \(n\le 29\). Still no leading-constant movement. Scripts: `research/ratio_scan.py`, `research/circulant_mitm.py`, `research/ratio_n7.py`, `research/leftover_stats.py`, `research/leftover_mcmc.py`, `research/lambda_leftover_and_circulants.py`.

As of 1 September 2026 the best proved bounds remain

\[
\Bigl(\tfrac12+o(1)\Bigr)\frac{k^2}{\log k}
\;\le\;
R(3,k)
\;\le\;
\bigl(1+o(1)\bigr)\frac{k^2}{\log k}.
\]

The lower bound is Hefty–Horn–King–Pfender, arXiv:2510.19718 v3 (existence via a random two-blow-up; not an explicit poly-time graph). The upper bound is Shearer, *Discrete Math.* 46 (1983). A January 2026 survey (Morris, arXiv:2601.05221) still quotes exactly this pair. The matching \(\tfrac12\) upper bound is a conjecture, not a theorem.

A breakthrough here means improving a **leading constant**: a lower bound \(>\tfrac12\), or an upper bound \(<1\). Second-order terms, explicit constructions weaker than HHKP, and finite-\(k\) tables do not count.

---

## 1. The two walls

### Lower-bound wall (cannot beat \(\tfrac12\) by a pseudorandom construction)

Write density \(p=c\sqrt{\log n/n}\) and \(\alpha\le A\sqrt{n\log n}\). The exchange rate is \(R(3,k)\ge(1/(2A^2)-o(1))k^2/\log k\). In any triangle-free graph, neighbourhoods are independent, so \(A\ge c\). In a graph that is random-like at this density the first moment gives \(A\ge 1/c\). Hence

\[
A(c)=\max\bigl(c,\,1/c\bigr)\;\ge\;1,
\]

with equality only at \(c=1\). HHKP sits exactly there. Their own remark: any construction beating \(\tfrac12\) would need **lower density and an independence number smaller than a random graph of that density**. No such object is known for any problem of this type.

Three or more “bites” do not help. The first moment sees only the **total** density. One blow-up is structurally broken (\(\alpha\) scales by the cluster size \(s\)). Two already break each other’s structure. Extra independent random blow-ups buy nothing on this side.

### Upper-bound wall (the remaining factor of \(2\))

Shearer proves \(\alpha(G)\ge\sum_v f(d_v)=(1+o(1))n\log d/d\) for triangle-free \(G\). Combined with \(\alpha\ge d\) this yields \(A\ge 1/\sqrt2\) and \(R(3,k)\le(1+o(1))k^2/\log k\).

A random graph of the same density has \(\alpha\sim 2n\log d/d\), twice the greedy value. Davies–Jenssen–Perkins–Roberts (2018) proved that even the **average** independent set has Shearer size:

\[
\alpha_G(1)\;\ge\;(1+o_d(1))\frac{\log d}{d}\,n.
\]

Their Conjecture 2 — \(\alpha(G)/\alpha_G(1)\ge 2-o_d(1)\) for min-degree \(d\to\infty\) — would give the matching upper bound \(R(3,k)\le(\tfrac12+o(1))k^2/\log k\). Conjecture 1 (\(\alpha/\alpha_G(1)\ge 4/3\)) would give \(3/4\). Both are open. Sahasrabudhe (arXiv:2512.15077, Dec 2025) still calls the optimal constant in Shearer a major open problem.

---

## 2. Attacks on the lower bound (trying \(>\tfrac12\))

None of these produce a graph with \(A<1\).

### 2.1 A third bite

Overlay three independent blow-ups of density \(p/3\). Total density \(p\), first-moment \(\alpha\) still \(\sim (2/p)\log(np)\). Same \(A(c)\). Two is already the first integer larger than one.

### 2.2 A non-random base graph

Replace \(G_R,G_B\sim G(m,p)\) by a triangle-free graph \(H\) with \(\alpha(H)\) smaller than random. That \(H\) is the object the construction is trying to build. Circular.

### 2.3 Algebraic / polarity bases

Polarity graphs of projective planes, strongly regular triangle-free graphs, Alon’s construction: these give \(\alpha=\Theta(\sqrt{n})\) or \(R(3,k)=\Omega(k^{3/2})\). Worse than HHKP by a \(\sqrt{k/\log k}\) factor. Spectral / Lovász \(\vartheta\) methods cannot reach SOTA: they do not see the \(\log\) in \(\sqrt{n\log n}\).

### 2.4 Explicit rewrite of HHKP

A counting rewrite of the two-bite existence proof is not an explicit construction and does not change the constant. Best proved poly-time explicit bound remains Alon \(\Omega(k^{3/2})\). Family L (if named) is exponential-time.

### 2.5 Push \(c>1\)

Past \(c=1\) neighbourhoods are independent sets of size \(c\sqrt{n\log n}\) and \(A\) rises. This is the neighbourhood lemma, not a defect of the method.

---

## 3. Attacks on the upper bound (trying \(<1\))

None of these improve the leading constant in Shearer.

### 3.1 Counting from the number of independent sets

Let \(\mu=n\log d/d\) and suppose \(\alpha\le(1+\delta)\mu\). Then

\[
\log i(G)\;\le\;(1+\delta)\mu\log\frac{en}{(1+\delta)\mu}\;=\;(1+\delta+o(1))\frac{n\log^2 d}{d}.
\]

DJPR (and the 2025 sharpening of Buys–van den Heuvel–Kang, arXiv:2503.10002) give only

\[
\log i(G)\;\ge\;\bigl(\tfrac12+o(1)\bigr)\frac{n\log^2 d}{d}.
\]

The trivial upper bound at \(\delta=0\) is twice the known lower bound, so the count is consistent with every independent set having Shearer size. Counting does not force \(\delta>0\).

### 3.2 Occupancy at large fugacity

The true occupancy \(\alpha_G(\lambda)\) increases in \(\lambda\) and \(\alpha_G(\lambda)\to\alpha(G)\) as \(\lambda\to\infty\). The DJPR *lower bound* on occupancy is not monotone in \(\lambda\) and is asymptotically \((1+o_d(1))\log d/d\) for all \(\lambda=O_d(1)\). Taking \(\lambda\to\infty\) in their formula does not produce a factor \(1+\delta\).

### 3.3 Two-pass greedy / local augmentation

Random greedy already achieves Shearer *on average* (Shearer’s Remark 1). A second pass that swaps a taken vertex for part of its neighbourhood is the neighbourhood bound \(\alpha\ge\Delta\), already optimised against greedy at \(d^2\sim n\log d\). Local search does not beat the leading constant.

### 3.4 Chromatic-number bounds

Molloy: \(\chi\le(1+o(1))d/\log d\) for triangle-free max-degree \(d\). Then \(\alpha\ge n/\chi\) recovers Shearer, not more. Random regular graphs have \(\chi\sim d/(2\log d)\), so Johansson–Molloy is not tight, but the *worst* triangle-free graph for \(\alpha\) is allowed to have \(\chi\) as large as \(d/\log d\).

### 3.5 A ratio \(\alpha/\alpha_G(1)\ge 1+\delta\)

This would give \(R(3,k)\le(1/(1+\delta)+o(1))k^2/\log k\). DJPR found no triangle-free example with ratio below \(1.432\ldots\) (the cyclic witness for \(R(3,9)\ge 36\)). That is experimental support for Conjecture 1, not a proof that the ratio is \(>1\) for every large-\(d\) triangle-free graph. The empty graph has ratio \(2\); the hard cases are dense triangle-free graphs.

### 3.6 Second-order terms

Shearer’s closed form is already \(f(d)=(\log d/d)(1-1/\log d+o(1/\log d))\), approaching from below. Feeding this into the exchange rate improves only the \(o(1)\) in \((1+o(1))k^2/\log k\), not the leading \(1\).

### 3.7 Induction on DJPR Conjecture 1 (ratio \(\ge 4/3\))

Write \(z=i(G)\) and \(a=\sum |I|\), so the average is \(a/z\) and the claim is \(\alpha z\ge(4/3)a\). For any vertex \(v\),
\[
z=z(G-v)+z(H),\qquad a=a(G-v)+a(H)+z(H),\qquad H=G-N[v],
\]
and \(\alpha(G)\ge\alpha(G-v)\), \(\alpha(G)\ge 1+\alpha(H)\). The independence polynomial of a disjoint union of triangles saturates \(4/3\), but those graphs *have* triangles; that is why the conjecture is plausible. The induction still does not close. In the case \(\alpha(G)=\alpha(G-v)=1+\alpha(H)\) one needs the slack
\[
\alpha\,z(G-v)-\tfrac43 a(G-v)\;\ge\;\tfrac13\,z(H).
\]
A single edge (the matching \(K_2\)) meets this with **equality** when you delete either vertex. There is no surplus to feed a stricter inductive loading. Stronger claims such as \(\alpha z-(4/3)a\ge cz\) fail already on \(K_2\).

Computations (not a proof):

| graph | \(n\) | \(\alpha\) | ratio \(\alpha/\mathrm{avg}\) |
|---|---|---|---|
| \(K_2\) | 2 | 1 | \(1.5\) |
| \(C_5\) | 5 | 2 | \(1.4667\) |
| Petersen | 10 | 4 | \(1.6889\) |
| Kalbfleisch circulant \(C_{35}(\pm1,\pm7,\pm11,\pm16)\) | 35 | 8 | \(1.43283\ldots\) (matches DJPR) |

No triangle-free example below \(4/3\) was found. The Kalbfleisch graph remains the smallest ratio in the literature. That is not a proof that every triangle-free graph sits above \(1+\delta\).

A complete enumeration of labelled triangle-free graphs on \(n\le 7\) (script `research/ratio_n7.py`) confirms the ratio is always at least \(C_5\)'s \(1.4667\). Finite, not asymptotic.

### 3.8 Occupancy at large fugacity, variance, and maximality

The factor \(2\) in Shearer vs a random graph is a **large-deviation** of the hard-core model, not a typical-set phenomenon. Under \(\mu_{G,1}\) the mass sits at size \(\sim n\log d/d\); sets of size \(\sim 2n\log d/d\) have expected count \(\Theta(1)\) and do not move the average. So \(\lambda=O_d(1)\) occupancy, even with a variance lower bound, stays at the Shearer constant: Davies–Jenssen–Perkins–Roberts already match the random regular graph there.

To see the extra factor you need \(\lambda=\lambda(d)\to\infty\). The DJPR formula gets *worse* as \(\lambda\) grows (the relaxation that \(Z\) may be constant is too pessimistic). Davies–Sandhu–Tan (arXiv:2505.13396, v2 Sep 2025) prove a degree-sequence occupancy bound only for \(\lambda\le c/\Delta^4\), and say explicitly that relaxing this to \(1/\log d\) would prove the Buys–van den Heuvel–Kang occupancy conjecture — they do not. Their variance bounds are likewise for \(\lambda=O(1/n)\). The April 2026 follow-up (arXiv:2604.01717) settles a variance comparison with \(K_n\), not \(R(3,k)\).

Maximal triangle-free graphs are the Ramsey-worst case (adding edges can only shrink \(\alpha\)). Regular maximal triangle-free graphs satisfy \(d^2\gtrsim n\). At the critical density \(d\sim\sqrt{n\log n}\) this is already true, and a typical non-edge has \(\sim\log n\) common neighbours — the same as \(G(n,p)\). Maximality does not add a first-order constraint at the Shearer point.

### 3.9 Leftover graph of a uniform independent set

This is the natural attack on the max-versus-average gap. Let \(I\) be uniform in \(\mathcal{I}(G)\) and let \(F=\{v:I\cap N[v]=\emptyset\}\) be the addable vertices. At fugacity \(1\), \(\mathbb{P}(v\text{ addable})=\mathbb{P}(v\in I)\), so \(\mathbb{E}|F|=\mathbb{E}|I|=\alpha_G(1)\). Pathwise \(\alpha(G)\ge|I|+\alpha(G[F])\). Caro–Wei on the leftover graph gives

\[
\alpha(G)\;\ge\;\mathbb{E}|I|+\mathbb{E}\sum_{v\in F}\frac1{1+d_{G[F]}(v)}.
\]

If leftover degrees were \(O(1)\), the second term would be a positive fraction of \(\alpha_G(1)\) and Shearer’s constant would move. Exact enumeration (Kalbfleisch \(C_{35}\), McGee, Petersen, Clebsch) and Glauber sampling (Hoffman–Singleton, cages, triangle-free process up to \(n=800\)) show that this does **not** happen.

On the Kalbfleisch graph (the worst known \(\alpha/\alpha_G(1)\) example, \(d=8\)) leftover mean degree is \(1.91\) and \(\mathbb{E}\alpha(G[F])/\mathbb{E}|I|=0.430\). That recovers \(\alpha\) almost exactly: \(\mathbb{E}|I|+\mathbb{E}\alpha(G[F])\approx 7.98\) against \(\alpha=8\). So leftover augmentation is tautological once \(\alpha(G[F])\) is computed exactly; the content has to come from a uniform lower bound on \(\alpha(G[F])\).

On triangle-free-process graphs the leftover mean degree grows, and the Caro–Wei surplus shrinks like \(1/\log d\):

| \(n\) | \(d\) | leftover mean deg | Caro–Wei / \(\mathbb{E}|I|\) | \(\approx 1.5/\log d\) |
|---|---|---|---|---|
| 30 | 8.7 | 1.12 | 0.641 | 0.69 |
| 120 | 20.4 | 1.75 | 0.496 | 0.50 |
| 200 | 28.2 | 1.97 | 0.460 | 0.45 |
| 400 | 41.7 | 2.35 | 0.403 | 0.40 |
| 800 | 62.0 | 2.70 | 0.357 | 0.36 |

The product \((\text{Caro–Wei}/\mathbb{E}|I|)\cdot\log d\) sits at \(1.4\)–\(1.5\). Relative extra \(\Theta(1/\log d)\) is not a leading constant. Recursing leftover (fill \(F\), then the leftover of that independent set, …) produces a geometric series with ratio \(1/\log d\), still \(1+o(1)\). Shearer on a leftover of degree \(\Theta(\log d)\) yields only an extra \(\mu\cdot(\log\log d)/\log d\).

High-girth cages are not a loophole for the Ramsey upper bound: a \(d\)-regular graph of girth \(\ge 6\) has \(n=\Omega(d^2)\), and Shearer already gives \(\alpha=\Omega(d\log d)\), far above \(k\sim d\). The only graphs that could threaten \(R(3,k)\le(1-\varepsilon)k^2/\log k\) already have the random number of \(C_4\)s. Those are exactly the graphs in the table.

McGee exact leftover (script-checked against Glauber): mean leftover degree \(1.420\), Caro–Wei ratio \(0.482\), matching the MCMC to three digits. Mixing is not the issue.

### 3.10 Occupancy slack versus pseudorandomness (no proof)

DJPR minimise occupancy over *all* random variables \(Z=\) (number of uncovered neighbours of a random vertex), not only those realised by a graph. The minimiser is concentrated \(Z\), and random regular graphs approximately achieve it, so occupancy at \(\lambda=O_d(1)\) cannot be improved in the leading constant. A case-split “either \(Z\) is concentrated, hence the graph is random-like and first-moment gives \(\alpha\sim 2\mu\), or occupancy has slack \(\ge(1+\delta)\mu\)” is the right *shape* of a proof of \(R(3,k)\le(\tfrac12+o(1))k^2/\log k\), but “concentrated uncovered-neighbour count \(\Rightarrow\) quasirandom enough for a first-moment at size \((1+\delta)\mu\)” is not shown. Random regular graphs *do* have both concentrated \(Z\) and \(\alpha\sim 2\mu\); making that implication uniform over all triangle-free graphs is DJPR Conjecture 2 in different clothes.

Triangle-free-only induction for a ratio \(c>4/3\) still fails in the branch \(\alpha(G)=\alpha(G-v)\): crude replacement of averages by maxima needs \(c\le 1\). The \(4/3\) slack identity is tight on \(K_2\) even among triangle-free graphs. Local Shearer (Martinsson–Steiner, arXiv:2501.00567) and the induced bipartite subgraph of min-degree \(\Omega(\log d)\) recover the same leading constant: two independent samples \(I,J\) give \(|I\cup J|\sim 2\mu\) with larger part \(\sim\mu\).

Literature through September 2026 (Morris survey arXiv:2601.05221; Buys–van den Heuvel–Kang arXiv:2503.10002; Davies–Sandhu–Tan occupancy) still quotes Shearer vs HHKP.

### 3.11 Fugacity tilt and circulant ratio census

The leftover collapse rate is the reason round 5 cannot give a leading constant. Writing \(L(k)\) for the average leftover size among independent \(k\)-sets, one has \((k+1)i_{k+1}=\sum |F(I)|\) so \(i_{k+1}/i_k=L(k)/(k+1)\). Adding a vertex to \(I\) removes \(1+d_F(v)\) leftover vertices. On triangle-free-process graphs \(d_F=\Theta(\log d)\) at the typical size \(k\sim\mu\), hence \(L\) drops at slope \(\Theta(\log d)\) and hits zero by \(k=\mu(1+O(1/\log d))\). A linear leftover model \(L(k)=2\mu-k\) would give \(\alpha=2\mu\) (DJPR Conjecture 2); the measured slope is too steep for a factor \(1+\delta\).

Tilting the hard-core measure to \(\lambda\neq 1\) does not repair this. Glauber on a triangle-free-process graph with \(n=200\), mean degree \(28.2\) (Shearer scale \(n\log d/d\approx 23.7\)):

| \(\lambda\) | \(\mathbb{E}|I|\) | leftover mean deg | \(\mathbb{E}|I|+\mathrm{CaroWei}(F)\) |
|---|---|---|---|
| 0.25 | 10.7 | 5.45 | 19.3 |
| 1 | 18.1 | 1.96 | 26.5 |
| 4 | 27.7 | 0.58 | 32.9 |
| 16 | 34.2 | 0.23 | 36.2 |

As \(\lambda\) grows, leftover becomes sparse but tiny; as \(\lambda\) shrinks, leftover is large but as dense as \(G\) itself. There is no \(\lambda\) at which leftover is both linear-sized and bounded-degree. The rise of \(\mathbb{E}|I|\) with \(\lambda\) on *this* graph is the expected large-deviation tilt toward \(\alpha\sim 2\mu\); DJPR’s Lambert-\(W\) occupancy lower bound at the same \(\lambda\) is far smaller, and they prove it is tight for some \(\lambda=O_d(1)\) graphs. A uniform occupancy improvement at \(\lambda=\Theta(1)\) is therefore unavailable.

Every inverse-closed triangle-free circulant on \(n\le 29\) was enumerated (connection sets of size \(\le 6\)). The smallest \(\alpha/\alpha_G(1)\) in that range is the \(4\)-regular \(C_{13}(\pm1,\pm5)\), the unique cyclic \(R(3,5)\)-witness:

\[
\alpha=4,\quad z=183,\quad \alpha/\mathrm{avg}=1.443787\ldots
\]

Three rotations of the same connection set, and three \(2\)-lifts on \(n=26\), repeat the ratio. Next is \(C_5\) at \(22/15=1.4667\). Nothing in the census undercuts Kalbfleisch’s \(1.43283\ldots\) on \(n=35\). Ratios do not drift toward \(1\) as \(n\) grows through this range. That is still only a census of circulants, not a proof that \(\inf\alpha/\alpha_G(1)>1\).

---

## 4. What a real proof would have to do

**To beat the lower bound.** Exhibit (randomly or explicitly) a triangle-free \(n\)-vertex graph with \(\alpha<(1-\varepsilon)\sqrt{n\log n}\) for some fixed \(\varepsilon>0\). Equivalently, a triangle-free graph that is *sparser* than HHKP and still has independent sets *smaller than a random graph of that density*. The notes’ barrier says no pseudorandom construction can do this.

**To beat the upper bound.** Prove that every triangle-free graph of large average degree \(d\) has \(\alpha\ge(1+\delta)n\log d/d\) for some fixed \(\delta>0\). The identified route is a uniform gap between the largest independent set and the average one (DJPR Conjectures 1–2). Occupancy, counting, greedy, and colouring, as they stand, all stop at the Shearer constant.

---

## 5. Honesty constraints (do not violate later)

- HHKP is SOTA for the **lower** bound only.
- Shearer 1983 is SOTA for the **upper** bound.
- The matching \(\tfrac12\) upper bound is a conjecture.
- HHKP is a random existence proof, not a poly-time explicit graph.
- Do not claim an algebraic / spectral / \(\vartheta\) family has \(\alpha=O(\sqrt{n\log n})\).
- A counting rewrite of HHKP is not an explicit SOTA construction.
- Best proved poly-time explicit bound remains Alon \(\Omega(k^{3/2})\).

This file is a log of failed attacks, not a claim that the constants have moved.
