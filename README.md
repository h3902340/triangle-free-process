# Triangle-Free Process — combinatorial lower bound for $R(3,t)$

This repository supports a presentation of Bohman's *triangle-free process* paper, with a **combinatorial proof** of the Ramsey lower bound
\[
R(3,t)\;\ge\; c\,\frac{t^2}{\log t}
\]
that avoids probabilistic process analysis and differential equations.

## Files

| File | Purpose |
|------|---------|
| [`PRESENTATION.md`](PRESENTATION.md) | Talk outline (~20 min), board summary, what to say |
| [`combinatorial-proof.tex`](combinatorial-proof.tex) | Self-contained write-up of the combinatorial proof |

## The idea in one paragraph

Bohman's differential equations predict that the density of open pairs after $t\,n^{3/2}$ steps is $\sim e^{-4t^2}$.
We realize the same density schedule in discrete **nibbles** of $\Theta(\gamma n^{3/2})$ open edges per round, track four combinatorial invariants by induction (the open-pair density evolves by the elementary product $\theta\leftarrow\theta\,e^{-4\gamma}$), and finish with a counting argument: every set of size $C\sqrt{n\log n}$ retains so many open pairs that some nibble is forced to hit it.
Averaging replaces martingales; a discrete product replaces the ODE.

## Theorem

There exists an absolute constant $c>0$ such that for all large $t$,
\[
R(3,t)\;\ge\; c\,\frac{t^2}{\log t}.
\]

(The constant here is weaker than the $\tfrac14-o(1)$ of Bohman–Keevash / Fiz Pontiveros–Griffiths–Morris; the order of magnitude is optimal.)

## Build the PDF

```bash
pdflatex combinatorial-proof.tex
```
