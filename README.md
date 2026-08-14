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
python3 explicit_family.py --n 50
python3 explicit_family.py 5
python3 explicit_family.py 13 --seed
python3 explicit_family.py 7 --diagnose
```

## Files

| File | Contents |
|------|----------|
| [`lean/`](lean/README.md) | Lean 4 + mathlib formalization of the **proved** Family A lemmas |
| [`EXPLICIT-STATUS.md`](EXPLICIT-STATUS.md) | One-page proved / not-proved list |
| [`DERANDOMIZATION.md`](DERANDOMIZATION.md) | Status of derandomization + concrete families |
| [`explicit-family.tex`](explicit-family.tex) | Family L (proved SOTA) and Family A (explicit) |
| [`family-a-independence.tex`](family-a-independence.tex) | Reduction + remaining lemma for $\alpha(A_q)$ |
| [`structured-cases.tex`](structured-cases.tex) | Structured seed sets and the shear fix |
| [`incidences.tex`](incidences.tex) | $G_2$-incidences of structured seed pairs |
| [`energy-increment.tex`](energy-increment.tex) | Structure vs randomness for $\alpha(G_R)$ |
| [`inverse-energy.tex`](inverse-energy.tex) | Medium-fibre clustering; exact/AP-cylinder packing; three-quarters energy; leftover |
| [`open-edges.tex`](open-edges.tex) | Sidon rewrite of the HHKP closed-pair buckets; medium stars reduce to seed energy |
| [`polytime-derandomization.tex`](polytime-derandomization.tex) | Deterministic poly-time two-bites algorithm (graph, not SOTA $\alpha$) |
| [`explicit_family.py`](explicit_family.py) | Constructor: `--n` or $q$ |
| [`sota-combinatorial.tex`](sota-combinatorial.tex) | Counting proof of the $\tfrac12$ bound |
| [`PRESENTATION.md`](PRESENTATION.md) | Talk outline for the Bohman-order combinatorial nibble |
| [`combinatorial-proof.tex`](combinatorial-proof.tex) | Combinatorial nibble proof of $\Omega(t^2/\log t)$ |
| [`hhkp-conjecture.tex`](hhkp-conjecture.tex) | Attempt at the HHKP $1/2$-conjecture (not a proof) |

## Lean-verified core

The lemmas that already have complete elementary proofs are formalized in
[`lean/`](lean/README.md) (Lean 4.33 + mathlib, no `sorry`). This includes the
fibre constraint, the corrected tight 4-interval (\(B=B+6\), hence empty or
the whole field for \(q>3\)), heavy-fibre exclusion, cycle packing, the
parabola Sidon property, the lift lemma, open-edge cleanup monotonicity,
the pairwise energy identity, one heavy off-diagonal pair (not an
\(\Omega(|T|^2)\) star), maximal-energy exact cylinders, the two-thirds
energy core, and the empty intermediate window at mean fibre size \(q/3\).

It does **not** verify the conjectural SOTA bound for Family A.

```bash
./scripts/setup-lean.sh
# or: cd lean && lake exe cache get && lake build
```

## Derandomization status

- **Counting existence proof of the SOTA $\tfrac12$ bound:** yes — see `sota-combinatorial.tex`.
- **Fully explicit construction at $\tfrac12$:** graph yes, bound no; best proved explicit remains $\Omega(k^{3/2})$ (Alon).
- **Lean-verified Family A core:** yes — see [`lean/README.md`](lean/README.md). Not a SOTA proof.
- **HHKP $1/2$-conjecture (upper bound):** not proved. Occupancy / bounded-fugacity methods are blocked; see [`hhkp-conjecture.tex`](hhkp-conjecture.tex).

## Build PDFs

```bash
pdflatex sota-combinatorial.tex
pdflatex combinatorial-proof.tex
```
