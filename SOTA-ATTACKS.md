# Attempts to beat the SOTA constants for \(R(3,k)\)

**Status: no unconditional breakthrough.** This note records the attacks that were tried and why they do not move either leading constant. It is not a theorem.

Round 2 attacked DJPR’s \(4/3\) ratio. Round 3 checked large-fugacity occupancy, DST variance bounds, maximality, and enumerated all triangle-free graphs on \(n\le 7\). Still no leading-constant movement. Scripts: `research/ratio_scan.py`, `research/circulant_mitm.py`, `research/ratio_n7.py`.

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
