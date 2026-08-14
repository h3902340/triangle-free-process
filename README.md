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

## Concrete families

| Family | Bound | Efficient? |
|--------|--------|------------|
| **L** — lex-first good HHKP configuration | SOTA $\tfrac12$, proved | no |
| **A** — algebraic two bites $A_q$ | SOTA $\tfrac12$, conjectural | yes |
| Alon Dual-BCH | $\Omega(k^{3/2})$, proved | yes |

See [`explicit-family.tex`](explicit-family.tex) and [`explicit_family.py`](explicit_family.py).

```bash
python3 explicit_family.py 5
```

## Files

| File | Contents |
|------|----------|
| [`DERANDOMIZATION.md`](DERANDOMIZATION.md) | Status of derandomization + concrete families |
| [`explicit-family.tex`](explicit-family.tex) | Family L (proved SOTA) and Family A (explicit) |
| [`family-a-independence.tex`](family-a-independence.tex) | Reduction + remaining lemma for $\alpha(A_q)$ |
| [`structured-cases.tex`](structured-cases.tex) | Structured seed sets and the shear fix |
| [`explicit_family.py`](explicit_family.py) | Constructor for $A_q$ |
| [`sota-combinatorial.tex`](sota-combinatorial.tex) | Counting proof of the $\tfrac12$ bound |
| [`PRESENTATION.md`](PRESENTATION.md) | Talk outline for the Bohman-order combinatorial nibble |
| [`combinatorial-proof.tex`](combinatorial-proof.tex) | Combinatorial nibble proof of $\Omega(t^2/\log t)$ |

## Derandomization status

- **Counting existence proof of the SOTA $\tfrac12$ bound:** yes — see `sota-combinatorial.tex`.
- **Fully explicit construction at $\tfrac12$:** no; best explicit remains $\Omega(k^{3/2})$ (Alon).

## Build PDFs

```bash
pdflatex sota-combinatorial.tex
pdflatex combinatorial-proof.tex
```
