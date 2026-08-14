# Triangle-Free Process / $R(3,t)$ lower bounds

Materials for presenting lower bounds on $R(3,t)$, including a **counting derandomization** of the current SOTA.

## SOTA (2025)

\[
\Bigl(\tfrac12+o(1)\Bigr)\frac{k^2}{\log k}
\;\le\;
R(3,k)
\;\le\;
\bigl(1+o(1)\bigr)\frac{k^2}{\log k}.
\]

- Lower: Hefty–Horn–King–Pfender, [arXiv:2510.19718](https://arxiv.org/abs/2510.19718) (“two bites”).
- Upper: Shearer (1983).

## Files

| File | Contents |
|------|----------|
| [`DERANDOMIZATION.md`](DERANDOMIZATION.md) | **Start here** for the SOTA derandomization attempt |
| [`sota-combinatorial.tex`](sota-combinatorial.tex) | Counting proof of the $\tfrac12$ bound (no prob language / no DE / no nibble) |
| [`PRESENTATION.md`](PRESENTATION.md) | Talk outline for the Bohman-order combinatorial nibble |
| [`combinatorial-proof.tex`](combinatorial-proof.tex) | Combinatorial nibble proof of $\Omega(t^2/\log t)$ (Bohman order) |

## Derandomization status

- **Counting existence proof of the SOTA $\tfrac12$ bound:** yes — see `sota-combinatorial.tex`.
- **Fully explicit construction at $\tfrac12$:** no; best explicit remains $\Omega(k^{3/2})$ (Alon).

## Build PDFs

```bash
pdflatex sota-combinatorial.tex
pdflatex combinatorial-proof.tex
```
