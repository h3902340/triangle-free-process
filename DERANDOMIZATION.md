# Derandomizing the SOTA lower bound — attempt

Target: Hefty–Horn–King–Pfender (arXiv:2510.19718)
\[
R(3,k)\ge\Bigl(\tfrac12+o(1)\Bigr)\frac{k^2}{\log k}.
\]

Full write-up: [`sota-combinatorial.tex`](sota-combinatorial.tex).

---

## Verdict

| Kind of derandomization | Result |
|-------------------------|--------|
| **Counting / existence** (no prob language, no DE, no nibble) | **Done** — same constant $\tfrac12$ |
| **Deterministic cleanup** | **Done** — already deterministic in HHKP |
| **Fully explicit construction** | **Not done** — still open; best explicit is $\Omega(k^{3/2})$ |

We derandomized the *proof style*. We did **not** produce an explicit graph family matching $\tfrac12$.

---

## What we did

1. Configuration space $\Omega$ = (graphs on $V_R$) × (graphs on $V_B$) × (injections $[n]\hookrightarrow V_R\times V_B$) is finite.
2. $\mathrm{Clean}(G_R,G_B,\varphi)$ is a deterministic triangle-deletion rule.
3. Chernoff / McDiarmid → binomial-fraction lemmas (counting tails).
4. Double count: fraction of configurations with $\alpha(\mathrm{Clean})\ge k$ is $o(1)$.
5. Hence some configuration yields a triangle-free $n$-vertex graph with $\alpha<(1+\varepsilon)\sqrt{n\log n}$.

No probability, no differential equations, no nibble, no martingales.

---

## Why full explicit derandomization fails (for now)

- Must kill $\binom{n}{k}=\exp\bigl(\Theta(\sqrt{n}(\log n)^{3/2})\bigr)$ potential independent sets.
- Any PRG fooling all of them needs seed $\Omega(\sqrt{n}(\log n)^{3/2})$.
- Spectral / $\vartheta$-function proofs cannot beat $\alpha=\Omega(n^{1/2})$ for triangle-free graphs → explicit barrier at $R(3,k)=\Omega(k^{3/2})$ (Alon).
- Polarity / Paley substitutes for $G_R,G_B$ have the wrong density or unproven independence-number control after the product step.

---

## Talk points (2–3 min)

> “The SOTA $\tfrac12$ bound can be told as a pure counting argument: average over two sparse graphs and an embedding, clean triangles by a fixed greedy rule, and count. That removes process analysis entirely. Turning the same argument into an explicit construction would break the long-standing $\Omega(k^{3/2})$ explicit-Ramsey barrier — we do not know how.”

---

## Files

| File | Role |
|------|------|
| `sota-combinatorial.tex` | Counting derandomization of HHKP |
| `combinatorial-proof.tex` | Earlier combinatorial nibble proof of Bohman-order bound |
| `PRESENTATION.md` | Original Bohman-oriented talk outline |
