# Derandomizing the SOTA lower bound

Target: Hefty–Horn–King–Pfender (arXiv:2510.19718)
\[
R(3,k)\ge\Bigl(\tfrac12+o(1)\Bigr)\frac{k^2}{\log k}.
\]

## Status

| Object | What is deterministic | SOTA \(\alpha\) | Time |
|--------|----------------------|-----------------|------|
| HHKP random two bites | cleanup only | **Theorem** (whp) | n/a (random) |
| Counting rewrite (`sota-combinatorial.tex`) | cleanup + existence | **Theorem** | n/a (counting) |
| **L** lex-first good config | entire graph | **Theorem** | exponential |
| **A** algebraic two bites | entire graph | **Conjecture** | \(\mathrm{poly}(n)\) |
| Alon Dual-BCH | entire graph | \(\Omega(k^{3/2})\) only | \(\mathrm{poly}(n)\) |

The construction is derandomized in polynomial time. The SOTA bound is not.

## Polynomial-time algorithm

On input \(n\), output the induced subgraph of \(A_q\) on the first \(n\) vertices, where \(q\) is the least odd prime with \(|A_q|\ge n\).

```bash
python3 explicit_family.py --n 50
python3 explicit_family.py 7 --diagnose
```

Details: [`polytime-derandomization.tex`](polytime-derandomization.tex).

**Proved:** triangle-free, degree \(O(\sqrt{n\log n})\), time \(\mathrm{poly}(n)\).

**Not proved:** \(\alpha(G_n)=O(\sqrt{n\log n})\). Leftovers: intermediate-energy fibres, medium-star incidences.

## Why not a PRG or conditional probabilities

A generator that fools every \(k\)-set needs seed length \(\Omega(\sqrt{n}\,(\log n)^{3/2})\). Enumerating those seeds is not polynomial. Method of conditional probabilities needs an efficiently computable proxy for surviving bad \(k\)-sets that keeps the constant \(\tfrac12\); none is known.

Family A is a different algorithm: replace the random seeds and the random injection by explicit algebra, then clean deterministically.

## Files

| File | Role |
|------|------|
| [`polytime-derandomization.tex`](polytime-derandomization.tex) | Algorithm, runtime, honesty bound |
| [`explicit_family.py`](explicit_family.py) | Constructor (`--n` or `q`) |
| [`explicit-family.tex`](explicit-family.tex) | Family L and Family A |
| [`sota-combinatorial.tex`](sota-combinatorial.tex) | Counting existence proof (Family L) |
| [`inverse-energy.tex`](inverse-energy.tex) | Seed leftover |
| [`open-edges.tex`](open-edges.tex) | Cleanup leftover |
